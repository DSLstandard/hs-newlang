module Vl.Parser where

import Data.Char (isDigit)
import Data.Char qualified as Char
import Data.Either.Extra (mapLeft)
import Data.List.NonEmpty qualified as NonEmpty
import Data.List.NonEmpty qualified as Unsafe
import Data.Set qualified as Set
import Data.Text qualified as T

import Error.Diagnose
import Error.Diagnose.Compat.Megaparsec

import GHC.RTS.Flags (CCFlags (doCostCentres))

import Prettyprinter

import Relude hiding (many, some)
import Relude.Extra (Foldable1 (foldr1), un)

import Text.Megaparsec
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L

import Vl.Common
import Vl.Expr
import Vl.Lens hiding (universe)
import Vl.Name
import Vl.TT

data ParseEnv
  = ParseEnv
      { parseEnvOrigin :: Origin
      }

makeFieldsNoPrefix ''ParseEnv

type Parser a = ReaderT ParseEnv (Parsec Void Text) a

instance HasHints Void msg where
  hints = absurd

runWrappedParser ::
  (IsString msg, Pretty msg) =>
  Parser a ->
  Origin ->
  Text ->
  Either (Diagnostic msg) a
runWrappedParser parser origin src =
  mapLeft
    ( \bundle -> do
        let diag = errorDiagnosticFromBundle Nothing "Parser Error" Nothing bundle
        addFile diag (toPath origin) (toString src)
    )
    (runParser (usingReaderT (ParseEnv origin) parser) (toPath origin) src)

scn :: Parser ()
scn = L.space C.space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

someNonEmpty :: Parser a -> Parser (NonEmpty a)
someNonEmpty p = NonEmpty.fromList <$> some p

sepNonEmpty :: Parser a -> Parser sep -> Parser (NonEmpty a)
sepNonEmpty p sep = NonEmpty.fromList <$> sepBy1 p sep

foldLine :: (Parser () -> Parser a) -> Parser a
foldLine = L.lineFold scn

indentBlock :: Parser a -> (Parser () -> a -> Parser r) -> Parser r
indentBlock ref handle = do
  startcol <- L.indentLevel
  a <- ref
  align <- option empty do
    aligncol <- try (L.indentGuard scn GT startcol)
    pure $ void $ L.indentGuard scn EQ aligncol
  handle align a

continueBlock :: Parser () -> (Parser () -> Parser r) -> Parser r
continueBlock sc handle = do
  align <- option empty do
    try sc
    aligncol <- L.indentLevel
    pure $ void $ L.indentGuard scn EQ aligncol
  handle align


startRange :: Parser (Parser Range)
startRange = do
  start <- getLoc
  origin <- asks parseEnvOrigin
  pure do
    end <- getLoc
    pure (Range start end origin)
  where
  getLoc :: Parser Loc
  getLoc = do
    SourcePos _ row col <- getSourcePos
    pure (Loc (unPos row, unPos col))

ranged :: Parser a -> Parser (Range, a)
ranged parser = do
  endRange <- startRange
  r <- parser
  range <- endRange
  pure (range, r)

ranging :: Parser (Range -> a) -> Parser a
ranging parser = do
  (range, r) <- ranged parser
  pure $ r range


inBetween :: Text -> Text -> Parser () -> Parser a -> Parser a
inBetween start end sc = between (symbol start) (symbol end) . between sc sc

inParens = inBetween "(" ")"
inBraces = inBetween "{" "}"
inBrackets = inBetween "[" "]"
inGraves = inBetween "`" "`"


keyword :: Text -> Parser ()
keyword kw = do
  C.string kw
  pass

symbol :: Text -> Parser ()
symbol sym = do
  C.string sym
  pass

username :: Parser Name
username = label "a username" do
  notFollowedBy $ satisfy isDigit -- without this, int literals may be parsed as a username
  c <- satisfy Char.isAlphaNum
  cs <- takeWhileP Nothing (\x -> Char.isAlphaNum x || any @[] (== x) "_-'")
  let str = T.cons c cs
  if str `Set.member` reservedKeywords
    then do
      failure
        (Just (Label $ NonEmpty.fromList $ "keyword '" <> toString str <> "'"))
        Set.empty
        -- (Set.singleton (Label $ NonEmpty.fromList "a username"))
    else
      pure (UserName str)

operatorName :: Parser Name
operatorName = do
  str <- takeWhile1P Nothing (`Set.member` allowedOperatorChars)
  if str `Set.member` reservedSymbols
    then do
      failure
        (Just (Label $ NonEmpty.fromList $ "symbol '" <> toString str <> "'"))
        Set.empty
        -- (Set.singleton (Label $ NonEmpty.fromList "an operator"))
    else
      pure (UserName str)

operator :: Parser AmbigName
operator = do
  try (inGraves pass ambigName) <|> fmap ambigNameSingleton operatorName

varname :: Parser Name
varname = label "variable name" do
  try (inParens pass operatorName) <|> username

ambigName :: Parser AmbigName
ambigName = do
  names <- sepNonEmpty varname (try (C.char '.')) -- TODO: lax the implementation to varname *> many?
  pure $ AmbigName (init names) (last names)

inImplicitInfo :: Parser () -> (ImplicitInfo -> Parser a) -> Parser a
inImplicitInfo sc run = asum
  [ inBraces sc (run IsImplicit)
  , inBrackets sc (run IsInstance)
  ]

inPiInfo :: Parser () -> (PiInfo -> Parser a) -> Parser a
inPiInfo sc run = asum
  [ inImplicitInfo sc (run . Implicit)
  , inParens sc (run Explicit)
  ]

multiParam :: Parser () -> Parser (NonEmpty EParam)
multiParam sc = ranging do
  asum
    [ inPiInfo sc \piinfo -> do
        names <- sepNonEmpty (ranged varname) (try (sc *> symbol ",") *> sc)
        sc
        symbol ":"
        sc
        argty <- expression sc
        pure \range ->
          fmap (\(namerange, name) -> EParam range piinfo name namerange argty) names
    -- , do
    --   guard $ allowtypehole == AllowTypeHole
    --   names <- sepNonEmpty
    --     (ranged varname)
    --     (try (sc *> symbol ",") *> sc)
    --   pure \range ->
    --     fmap (\(namerange, name) -> EParam range Explicit name namerange (EHole range)) names
    ]

fullParams :: Parser () -> Parser (NonEmpty EParam)
fullParams sc = do
  params <- paramsPart
  params's <- many $ try $ sc *> paramsPart
  pure $ sconcat $ params :| params's
  where
  single :: Parser EParam
  single = ranging $ asum
    [ do
        (imp, (namerange, name)) <- inImplicitInfo sc $ \imp -> (imp,) <$> ranged varname -- NOTE: inPiInfo works too, so `(a)` are allowed to
        pure $ \range -> EParam range (Implicit imp) name namerange (EHole namerange)
    , do
        (namerange, name) <- ranged varname
        pure $ \range -> EParam range Explicit name namerange (EHole namerange)
    ]

  paramsPart :: Parser (NonEmpty EParam)
  paramsPart = try (multiParam sc) <|> fmap NonEmpty.singleton single

hole :: Parser Expr
hole = do
  (range, _) <- ranged $ symbol "_"
  pure $ EHole range

type' :: Parser Expr
type' = do
  (range, _) <- ranged $ keyword "Type"
  pure $ EType range

variable :: Parser Expr
variable = do
  (range, ambigname) <- ranged ambigName
  pure $ EVar range ambigname

namedPi :: Parser () -> Parser Expr
namedPi sc = do
  endRange <- startRange
  params <- try do
    r <- multiParam sc
    sc
    symbol "->"
    pure r
  sc
  retty <- expression sc
  range <- endRange
  pure $ foldr1 (EPi range) retty params

lam :: Parser () -> Parser Expr
lam sc = do
  ranging do
    symbol "\\"
    params <- fullParams sc
    sc
    symbol "=>"
    sc
    body <- expression sc
    pure $ \range -> foldr1 (ELam range) body params

case' :: Parser () -> Parser Expr
case' sc = ranging do
  scrutinee <- headline
  continueBlock sc \align -> do
    clauses <- many $ try align *> clause
    pure $ \range -> ECase $ ECaseBase range scrutinee clauses
    -- scrutinee
    -- clauses <- many $ do
    --   try align
    --   ranging $ foldLine \sc -> do
    --     lhs <- application sc
    --     sc
    --     symbol "=>"
    --     sc
    --     rhs <- expression sc
    --     pure \range -> EClause range lhs rhs
    -- pure \range -> undefined
  where
  headline :: Parser Expr
  headline = do
    keyword "case"
    sc
    scr <- expression sc
    sc
    keyword "of"
    pure scr

  clause :: Parser EClause
  clause = ranging $ foldLine \sc -> do
    lhs <- expression sc
    sc
    symbol "=>"
    sc
    rhs <- expression sc
    pure \range -> EClause range lhs rhs

let' :: Parser () -> Parser Expr
let' sc = ranging do
  keyword "let"
  sc
  tomatch <- expression sc
  sc
  symbol "="
  sc
  scrutinee <- expression sc
  sc
  keyword "in"
  sc
  body <- expression sc
  pure $ \range -> ELet $ ECaseBase range scrutinee [EClause range tomatch body]

userHole :: Parser Expr
userHole = ranging do
  C.char '?'
  name <- username
  pure \range -> EUserHole range name

stringLit :: Parser Text
stringLit = label "string literal" do
  fmap T.pack $ C.char '"' *> manyTill L.charLiteral (C.char '"')

charLit :: Parser Char
charLit = label "char literal" do
  C.char '\'' *> L.charLiteral <* C.char '\''

intLit :: Parser Integer
intLit = label "integer literal" do
  L.signed pass $ asum
    [ C.string "0x" *> L.hexadecimal
    , C.string "0o" *> L.octal
    , C.string "0b" *> L.binary
    , L.decimal
    ]

primitiveType :: Parser PrimitiveType
primitiveType = asumMap go (universe @PrimitiveType)
  where
  go :: PrimitiveType -> Parser PrimitiveType
  go x = keyword (primitiveTypeWord x) $> x

primitive :: Parser Primitive
primitive = asum
  [ PType   <$> primitiveType
  , PString <$> stringLit
  , PChar   <$> charLit
  , PInt    <$> intLit
  ]

prim :: Parser Expr
prim = ranging do
  x <- primitive
  pure $ \range -> EPrim range x


data EDoLine
  = EDoLineVoid
      { _range      :: Range
      , _expression :: Expr
      }
  | EDoLineBind
      { _range      :: Range
      , _name       :: Name
      , _nameRange  :: Range
      , _expression :: Expr
      }
  deriving (Show)


do' :: Parser () -> Parser Expr
do' sc = do
  keyword "do"
  continueBlock sc \align -> do
    lines <- someNonEmpty do
      try align
      doLine
    foldDoLines lines
  where
  underLine :: EDoLine -> Expr -> Expr
  underLine line next =
    case line of
      EDoLineVoid range expr -> do
        let apprange = range <> exprRange next
        exprFoldExplicitSpine apprange
          (EVar apprange ">>=")
          [ expr
          , ELam range (EParam range Explicit boringName range (EHole range)) next
          ]
      EDoLineBind range name namerange expr -> do
        let apprange = range <> exprRange next
        exprFoldExplicitSpine apprange
          (EVar apprange ">>=")
          [ expr
          , ELam range (EParam range Explicit name namerange (EHole namerange)) next
          ]

  foldDoLines :: NonEmpty EDoLine -> Parser Expr
  foldDoLines (line :| []) =
    case line of
      EDoLineVoid range expr -> pure expr
      EDoLineBind range namerange name expr ->
        fail "last line of do must be a void expression"
  foldDoLines (line :| (x : xs)) = do
    next <- foldDoLines (x :| xs)
    pure $ underLine line next

  doLine :: Parser EDoLine
  doLine = doLineBind <|> doLineVoid

  doLineBind :: Parser EDoLine
  doLineBind = ranging $ foldLine \sc -> do
    (namerange, name) <- try do
      r <- ranged varname
      sc
      symbol "<-"
      pure r
    sc
    expr <- expression sc
    pure $ \range -> EDoLineBind range name namerange expr

  doLineVoid :: Parser EDoLine
  doLineVoid = ranging  $ foldLine \sc -> do
    expr <- expression sc
    pure $ \range -> EDoLineVoid range expr


nonApplication :: Parser () -> Parser Expr
nonApplication sc = asum
  [ hole
  , type'
  , prim
  , lam sc
  , let' sc
  , case' sc
  , do' sc
  , userHole
  , variable
  , namedPi sc
  , inParens sc $ expression sc
  ]

applicationArg :: Parser () -> Parser EArg
applicationArg sc = do
  endRange <- startRange
  asum
    [ EArg <$> endRange <*> pure TheImplicit <*> inBraces sc (expression sc)
    , EArg <$> endRange <*> pure TheExplicit <*> nonApplication sc
    ]

application :: Parser () -> Parser Expr
application sc = do
  endRange <- startRange
  fn <- nonApplication sc
  args <- many $ try do
    sc
    arg <- applicationArg sc
    range <- endRange
    pure (range, arg)
  pure $ foldl' (\fn' (range, arg') -> EApp range fn' arg') fn args

expression :: Parser () -> Parser Expr
expression sc = do
  endRange <- startRange
  first <- application sc
  asum
    [ restAsPi endRange first
    , restAsOp first
    , pure first
    ]
  where
  restAsPi endRange first = do
    try do
      sc
      symbol "->"
    sc
    rest <- expression sc
    EPi <$> endRange <*> pure (EParam (exprRange first) Explicit boringName (exprRange first) first) <*> pure rest

  restAsOp left = do
    (oprange, op) <- try do
      sc
      ranged operator
    sc
    right <- expression sc
    pure $ EOpTree left op oprange right

userExpression :: Parser Expr
userExpression = do
  L.nonIndented scn (foldLine expression) <* scn <* eof


claim :: Parser EClaim
claim = foldLine \sc -> do
  endRange <- startRange
  (namerange, name) <- try do
    r <- ranged varname
    sc
    symbol ":"
    pure r
  sc
  ty <- expression sc
  range <- endRange
  pure $ EClaim range name namerange ty

data' :: Parser EData
data' = do
  indentBlock headline \align tycon -> do
    asum
      [ do
        try align
        symbol "[external]"
        pure $ EData tycon EInhabit_External
      , do
        cons <- many (try align *> constructor)
        pure $ EData tycon (EInhabit_DataCons cons)
      ]
  where
  headline :: Parser EConstructor
  headline = foldLine \sc -> do
    keyword "data"
    sc
    tycon <- constructor
    sc
    keyword "where"
    pure tycon

  constructor :: Parser EConstructor
  constructor = do
    ranging $ foldLine \sc -> do
      (namerange, name) <- ranged varname
      sc
      symbol ":"
      sc
      ty <- expression sc
      pure $ \range -> EConstructor range name namerange ty

clause :: Parser EClause
clause = do
  ranging $ foldLine \sc -> do
    lhs <- try do
      r <- expression sc
      sc
      symbol "="
      pure r
    sc
    rhs <- expression sc
    pure $ \range -> EClause range lhs rhs

structBase :: Text -> Parser EStructBase
structBase kw = do
  indentBlock
    ( foldLine \sc -> do
        keyword kw
        sc
        (tycnamerange, tycname) <- ranged varname
        sc
        tycparams <- option [] (toList <$> fullParams sc)
        sc
        keyword "where"
        pure (tycname, tycnamerange, tycparams)
    )
    ( \align (tycname, tycnamerange, tycparams) -> do
        (dtcnamerange, dtcname) <- constructor align tycnamerange tycname
        dtcparams <- many $ try align *> dtParam
        pure $ EStructBase tycname tycnamerange tycparams dtcname dtcnamerange dtcparams
    )
  where
  constructor align tycnamerange tycname = option
    (tycnamerange, UserName ("Mk" <> nameRoot tycname)) -- default constructor name
    ( foldLine \sc -> do
        try align
        keyword "constructor"
        sc
        ranged varname
    )

  dtParam :: Parser EParam
  dtParam = foldLine \sc -> do
    asum
      [ inImplicitInfo sc \piinfo -> typed sc (Implicit piinfo)
      , typed sc Explicit
      ]

  typed sc piinfo = do
    endRange <- startRange
    (namerange, name) <- ranged varname
    sc
    symbol ":"
    sc
    ty <- expression sc
    range <- endRange
    pure $ EParam range piinfo name namerange ty

fixity' :: Parser EFixity
fixity' = ranging $ foldLine \sc -> do
  fixity <- fixity
  sc
  precedence <- L.decimal
  sc
  (oprange, op) <- ranged operator
  let opinfo = OpInfo fixity precedence
  pure $ \range -> EFixity range opinfo op oprange
  where
  fixity :: Parser Fixity
  fixity = asum
    [ Infixl <$ keyword "infixl"
    , Infixr <$ keyword "infixr"
    , Infix  <$ keyword "infix" -- do this last because common prefix
    ]

instance' :: Parser EInstance
instance' = ranging $ foldLine \sc -> do
  keyword "instance"
  sc
  (namerange, name) <- ranged ambigName
  pure $ \range -> EInstance range name namerange

namespace :: Parser ENamespace
namespace = do
  indentBlock headline \align n -> do
    defs <- many (try align *> definition)
    pure $ ENamespace n defs
  where
  headline :: Parser Name
  headline = foldLine \sc -> do
    keyword "namespace"
    sc
    n <- varname
    sc
    keyword "where"
    pure n

definition :: Parser EDef
definition = asum
  [ EDefData <$> data'
  , EDefStruct <$> structBase "struct"
  , EDefInterface <$> structBase "interface"
  , EDefFixity <$> fixity'
  , EDefInstance <$> instance'
  , EDefNamespace <$> namespace
  -- definitions that are *likely* not prefixed by a keyword
  , EDefClaim <$> claim
  , EDefClause <$> clause
  ]

userFile :: Parser EFile
userFile = do
  defs <- manyTill (L.nonIndented scn definition) (try (scn *> eof))
  pure $ EFile defs
