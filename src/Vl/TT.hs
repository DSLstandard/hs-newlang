module Vl.TT where

import Control.Algebra
import Control.Effect.Reader qualified as C

import Data.HashMap.Strict qualified as HashMap
import Data.Set qualified as Set
import Data.Text qualified as T

import Prettyprinter
import Prettyprinter.Render.Terminal

import Relude

import Utils
import Utils.Pretty

import Vl.Common
import Vl.Lens
import Vl.Name

data Param a
  = Param
      { _piInfo  :: PiInfo
      , _name    :: Name
      , _argType :: Type' a
      }
  deriving (Foldable, Functor, Show, Traversable)
makeFieldsNoPrefix ''Param

type Dej = Int
type Level = Int


data Primitive
  = PChar !Char
  | PString !Text
  | PInt !Integer
  | PType PrimitiveType
  deriving (Eq, Show)

typeOfPrim :: Primitive -> Type' Term
typeOfPrim (PType _)   = TType
typeOfPrim (PChar _)   = Prim $ PType PCharType
typeOfPrim (PString _) = Prim $ PType PStringType
typeOfPrim (PInt _)    = Prim $ PType PIntType

data Term' z
  = TType
  -- | this is primarily for internal use
  | Bound Name
  | Var Dej
  | App (Term' z) (Term' z)
  | Pi (Param (Term' z)) (Type' (Term' z))
  | Lam Name (Term' z)
  | Func QName
  | Con ConInfo QName
  | Meta QName
  | Prim Primitive
  | Alien z
  deriving (Foldable, Functor, Show, Traversable)

type Term = Term' Void

foldSpine :: Term' z -> [Term' z] -> Term' z
foldSpine = foldl' App

unfoldSpine :: Term' z -> (Term' z, [Term' z])
unfoldSpine = go []
  where
  go acc (App f x) = go (x : acc) f
  go acc f         = (f, acc)

------------------------------------------------------------------------
-- * GeneralizeAlien
------------------------------------------------------------------------

class GeneralizeAlien f where
  generalizeAlien :: f Void -> f z
  default generalizeAlien :: Functor f => f Void -> f z
  generalizeAlien = fmap absurd

instance GeneralizeAlien Term' where

------------------------------------------------------------------------
-- * CaseTree
------------------------------------------------------------------------

type ArgNames = [Name]

-- | constructor name to arm
type CaseArms = HashMap.HashMap QName CaseArm

data CaseTree' z
  = CaseOn Dej CaseArms
  | CaseScope (Term' z)
  | CaseUnhandled
  deriving (Foldable, Functor, Show, Traversable)
type CaseTree = CaseTree' Void

data CaseArm' z
  = CaseDtCon
      { _conName  :: QName
      , _argNames :: ArgNames
      , _tree     :: CaseTree' z
      }
  deriving (Foldable, Functor, Show, Traversable)
type CaseArm = CaseArm' Void

data PatternFunc
  = PatternFunc
      { _argNames :: ArgNames
      , _tree     :: CaseTree
      }

fromSolution :: Closed Term -> PatternFunc
fromSolution = PatternFunc [] . CaseScope

makeFieldsNoPrefix ''CaseArm'
makeFieldsNoPrefix ''PatternFunc

fromCaseArmList :: [CaseArm] -> CaseArms
fromCaseArmList =
  HashMap.fromList . fmap (\arm -> (arm^.conName, arm))

instance GeneralizeAlien CaseTree' where
instance GeneralizeAlien CaseArm' where

renderCaseArm :: GammaNames -> CaseArm -> Doc AnsiStyle
renderCaseArm gamma CaseDtCon{..} =
  hsep (acon (pretty _conName) : fmap (alocal . pretty) _argNames)
    <+> asymbol "=>"
    <+> renderCaseTree (reverse _argNames <> gamma) _tree

renderCaseTree :: GammaNames -> CaseTree -> Doc AnsiStyle
renderCaseTree gamma CaseUnhandled = aspecial "<!!unhandled!!>"
renderCaseTree gamma (CaseScope tm) = renderTerm gamma tm
renderCaseTree gamma (CaseOn dej arms) = do
  nest 2 $ vsep
    ( akeyword "case" <+> renderVar gamma dej <+> akeyword "of"
    : fmap (renderCaseArm gamma) (HashMap.elems arms)
    )

renderPatternFunc :: Name -> PatternFunc -> Doc AnsiStyle
renderPatternFunc fnname (PatternFunc argnames tree) = do
  hsep (afunc (pretty fnname) : fmap (alocal . pretty) argnames)
    <+> asymbol "="
    <+> renderCaseTree (reverse argnames) tree

------------------------------------------------------------------------
-- * ToLevel
------------------------------------------------------------------------

class ToLevel a where
  levelOf :: a -> Level

instance ToLevel Name where
  levelOf n = 1

instance ToLevel [Name] where
  levelOf = length

instance ToLevel (Param a) where
  levelOf p = 1

instance ToLevel [Param a] where
  levelOf = length

------------------------------------------------------------------------
-- * Weakening
------------------------------------------------------------------------

class WeakenAfter a where
  weakenAfter :: Level -> Level -> a -> a

weakenAfterBy :: (WeakenAfter a, ToLevel off, ToLevel lvl) => off -> lvl -> a -> a
weakenAfterBy off lvl = weakenAfter (levelOf off) (levelOf lvl)

class Weaken a where
  weaken :: Level -> a -> a
  default weaken :: WeakenAfter a => Level -> a -> a
  weaken = weakenAfter 0

weakenBy :: (Weaken a, ToLevel lvl) => lvl -> a -> a
weakenBy lvl = weaken (levelOf lvl)

instance Weaken a => Weaken [a] where
  weaken lvl = fmap $ weaken lvl
instance WeakenAfter a => WeakenAfter [a] where
  weakenAfter off lvl = fmap $ weakenAfter off lvl

instance Weaken Dej where
instance WeakenAfter Dej where
  weakenAfter off lvl i
    = if i < off then i else i + lvl

instance Weaken (Term' z) where
instance WeakenAfter (Term' z) where
  weakenAfter off lvl = \case
    Prim x  -> Prim x
    Alien x -> Alien x
    TType   -> TType
    Var i   -> Var $ weakenAfter off lvl i
    Meta n  -> Meta n
    Func n  -> Func n
    Con c n -> Con c n
    Bound n -> Bound n
    App f x -> App (weakenAfter off lvl f) (weakenAfter off lvl x)
    Pi a b  -> Pi (weakenAfter off lvl a) (weakenAfter (weakenBy a off) lvl b)
    Lam n b -> Lam n (weakenAfter (weakenBy n off) lvl b)

instance Weaken a => Weaken (Param a) where
  weaken lvl = fmap $ weaken lvl
instance WeakenAfter a => WeakenAfter (Param a) where
  weakenAfter off lvl = fmap $ weakenAfter off lvl

------------------------------------------------------------------------
-- * CollectMetas
------------------------------------------------------------------------

class CollectMetas a where
  collectMetas :: a -> Set.Set QName

instance CollectMetas a => CollectMetas (Param a) where
  collectMetas = foldMap collectMetas

instance CollectMetas (Term' z) where
  collectMetas (Alien x)        = mempty
  collectMetas (Prim x)         = mempty
  collectMetas (Meta n)         = Set.singleton n
  collectMetas TType            = mempty
  collectMetas (App f x)        = collectMetas f <> collectMetas x
  collectMetas (Bound n)        = mempty
  collectMetas (Func n)         = mempty
  collectMetas (Con c n)        = mempty
  collectMetas (Var i)          = mempty
  collectMetas (Pi param scope) = collectMetas param <> collectMetas scope
  collectMetas (Lam n scope)    = collectMetas scope

------------------------------------------------------------------------
-- * Context
------------------------------------------------------------------------

type Context = [Param Term]
type SubContext = [Param Term]
type GammaNames = [Name]
type GotContext sig m = Has (C.Reader Context) sig m

lams :: Level -> Term -> Closed Term
lams 0 tm   = tm
lams lvl tm = lams (lvl - 1) $ Lam (VirtName "i" (lvl - 1)) tm -- designed to have an ascending order of lam names

lamsNamed :: GammaNames -> Term -> Closed Term
lamsNamed ns tm = foldl' (flip Lam) tm ns

contextFlatten :: Context -> [(Dej, Param Term)]
contextFlatten = go 0
  where
  go :: Level -> Context -> [(Dej, Param Term)]
  go lvl [] = []
  go lvl (param : params) =
    let lvl' = lvl + 1 in (lvl, weaken lvl' param) : go lvl' params

contextLookupBy :: (Name -> Bool) -> Context -> [(Dej, Param Term)]
contextLookupBy pred = filter (\(i, m) -> pred (m^.name)) . contextFlatten

contextGammaNames :: Context -> GammaNames
contextGammaNames = toListOf (traverse.name)

contextSub :: Level -> Context -> SubContext
contextSub 0 ctx       = []
contextSub j []        = error "context is not large enough"
contextSub j (p : ctx) = p : contextSub (j-1) ctx

contextAtSured :: Dej -> Context -> Param Term
contextAtSured i ctx = snd $ contextFlatten ctx^?! ix i

abstractPis :: Type' Term -> Context -> Closed (Type' Term)
abstractPis = flipfoldl' Pi

constArgs :: Level -> [Term]
constArgs 0   = []
constArgs lvl = let lvl' = lvl - 1 in Var lvl' : constArgs lvl'

emptyContext :: Context
emptyContext = []

currentContext :: GotContext sig m => m Context
currentContext = C.ask

underParam :: GotContext sig m => Param Term -> m a -> m a
underParam param = C.local @Context (param :)

scrutineeName :: Name
scrutineeName = VirtName "scrutinee" 0

underScrutinee :: GotContext sig m => Type' Term -> m a -> m a
underScrutinee scrty = underParam (Param Explicit scrutineeName scrty)

underTelescopeWhere :: GotContext sig m => (Param Term -> Bool) -> Type' Term -> (GammaNames -> Type' Term -> m a) -> m a
underTelescopeWhere f = go []
  where
  go gamma (Pi a b) act | f a = underParam a $ go ((a^.name) : gamma) b act
  go gamma t act              = act gamma t

underTelescope :: GotContext sig m => Type' Term -> (GammaNames -> Type' Term -> m a) -> m a
underTelescope = underTelescopeWhere (const True)

extendContext :: GotContext sig m => Context -> m a -> m a
extendContext ctx = C.local @Context (ctx <>)

------------------------------------------------------------------------
-- * Rendering
------------------------------------------------------------------------

alocal = annotate (color Green)
akeyword = annotate (color Red <> bold)
asymbol = annotate (color Red)
abound = annotate (color Blue <> italicized)
ameta = annotate (color Cyan <> italicized)
acon = annotate (color Cyan <> bold)
afunc = annotate (color Blue)
aspecial = annotate (color Red)
aliteral = annotate (color Red)

renderVar :: GammaNames -> Dej -> Doc AnsiStyle
renderVar gamma dej =
  alocal $ maybe
    (brackets (pretty dej))
    (\n -> pretty n <> pretty (T.map subscript (show dej)))
    (gamma^?ix dej)

renderImplicitInfo :: ImplicitInfo -> Doc AnsiStyle -> Doc AnsiStyle
renderImplicitInfo IsImplicit body = asymbol "{" <> body <> asymbol "}"
renderImplicitInfo IsInstance body = asymbol "[" <> body <> asymbol "]"

renderPiInfo :: PiInfo -> Doc AnsiStyle -> Doc AnsiStyle
renderPiInfo Explicit     body = asymbol "(" <> body <> asymbol ")"
renderPiInfo (Implicit i) body = renderImplicitInfo i body

renderParam :: Pretty z => GammaNames -> Param (Term' z) -> Doc AnsiStyle
renderParam gamma (Param p n t) =
  renderPiInfo p $ alocal (pretty n) <+> asymbol ":" <+> renderTerm gamma t

renderPrimitiveType :: PrimitiveType -> Doc AnsiStyle
renderPrimitiveType = akeyword . pretty . primitiveTypeWord

renderPrimitive :: Primitive -> Doc AnsiStyle
renderPrimitive (PType x)   = renderPrimitiveType x
renderPrimitive (PChar x)   = aliteral (show x)
renderPrimitive (PString x) = aliteral (show x)
renderPrimitive (PInt x)    = aliteral (show x)

renderTerm :: Pretty z => GammaNames -> Term' z -> Doc AnsiStyle
renderTerm gamma (Alien z) = aspecial $ angles (pretty z)
renderTerm gamma (Prim x) = renderPrimitive x
renderTerm gamma TType = akeyword "Type"
renderTerm gamma (Bound n) = abound (pretty n)
renderTerm gamma (Meta n) = ameta ("?" <> pretty n)
renderTerm gamma (Var dej) = renderVar gamma dej
renderTerm gamma (Pi param retty) =
  paramdoc <+> asymbol "->" <+> renderTerm ((param^.name) : gamma) retty
  where
  paramdoc = case (param^.piInfo, isNameBoring (param^.name)) of
    (Explicit, True) -> renderTerm gamma (param^.argType)
    _                -> renderParam gamma param
renderTerm gamma lam@Lam{} =
  asymbol "λ"
    <> (separatedBy (asymbol ", ") (alocal . pretty <$> ns))
    <+> asymbol "=>" <+> renderTerm (reverse ns <> gamma) body
  where
  (ns, body) = collectLams lam

  collectLams :: Term' z -> ([Name], Term' z)
  collectLams (Lam n body) = first (n :) (collectLams body)
  collectLams tm           = ([], tm)
renderTerm gamma (Func n) = afunc (pretty n)
renderTerm gamma (Con c n) = acon (pretty n)
renderTerm gamma (App fn arg) = go fnambig fn <+> go argambig arg
  where
  go f x = (bool id parens f) (renderTerm gamma x)
  fnambig = case fn of
    Pi{}  -> True
    Lam{} -> True
    _     -> False
  argambig = case arg of
    Pi{}  -> True
    Lam{} -> True
    App{} -> True
    _     -> False

renderContext :: Context -> Doc AnsiStyle
renderContext [] = aspecial "<empty context>"
renderContext ctx = list $ reverse $ renderAll ctx
  where
  renderAll [] = []
  renderAll (param : ctx) =
    renderParam (contextGammaNames ctx) param : renderAll ctx

------------------------------------------------------------------------
-- * UnifyConstraint
------------------------------------------------------------------------

data UnifyConstraint
  = UnifyConstraint
      { _gamma :: GammaNames
      , _lhs   :: Term
      , _rhs   :: Term
      }
makeFieldsNoPrefix ''UnifyConstraint

renderUnifyConstraint :: UnifyConstraint -> Doc AnsiStyle
renderUnifyConstraint (UnifyConstraint gamma lhs rhs) =
  renderTerm gamma lhs <+> asymbol "~" <+> renderTerm gamma rhs

------------------------------------------------------------------------
-- * SubstEnv
------------------------------------------------------------------------

type SubstEnv = [Term]

class SubstAfter a where
  substAfter :: Level -> SubstEnv -> a -> a

subst :: SubstAfter a => SubstEnv -> a -> a
subst = substAfter 0

substDej :: SubstEnv -> Dej -> Term
substDej [] dej      = Var dej
substDej (x : env) 0 = x
substDej (x : env) i = substDej env (i - 1)

substDejAfter :: Level -> SubstEnv -> Dej -> Term
substDejAfter off env i =
  if i < off then Var i else weaken off $ substDej env (i - off)

instance SubstAfter a => SubstAfter (Param a) where
  substAfter off env = fmap (substAfter off env)

instance SubstAfter Term where
  substAfter off env (Alien x) = Alien x
  substAfter off env (Prim x) = Prim x
  substAfter off env TType = TType
  substAfter off env (Func n) = Func n
  substAfter off env (Con c n) = Con c n
  substAfter off env (Bound n) = Bound n
  substAfter off env (Meta n) = Meta n
  substAfter off env (App fn arg) =
    App (substAfter off env fn) (substAfter off env arg)
  substAfter off env (Var dej) = substDejAfter off env dej
  substAfter off env (Lam n scope) =
    Lam n (substAfter (off + 1) env scope)
  substAfter off env (Pi param scope) =
    Pi (substAfter off env param) (substAfter (off + 1) env scope)

------------------------------------------------------------------------
-- * ReplaceBound
------------------------------------------------------------------------

data BoundReplace
  = BoundReplace Name Term

instance Weaken BoundReplace where
  weaken lvl (BoundReplace n tm) = BoundReplace n (weaken lvl tm)

class ReplaceBound a where
  replaceBounds :: [BoundReplace] -> a -> a

instance ReplaceBound a => ReplaceBound (Param a) where
  replaceBounds reps = fmap $ replaceBounds reps

instance ReplaceBound Term where
  replaceBounds reps (Bound n) =
    case find (\(BoundReplace n' tm) -> n == n') reps of
      Nothing                  -> Bound n
      Just (BoundReplace _ tm) -> tm
  replaceBounds reps (Var i) = Var i
  replaceBounds reps (Alien x) = Alien x
  replaceBounds reps (Prim x) = Prim x
  replaceBounds reps (App f x) = App (replaceBounds reps f) (replaceBounds reps x)
  replaceBounds reps (Lam n e) = Lam n (replaceBounds (weakenBy n reps) e)
  replaceBounds reps (Pi a b) = Pi (replaceBounds reps a) (replaceBounds (weakenBy a reps) b)
  replaceBounds reps TType = TType
  replaceBounds reps (Func n) = Func n
  replaceBounds reps (Con c n) = Con c n
  replaceBounds reps (Meta n) = Meta n

------------------------------------------------------------------------
-- * ReplaceVar
------------------------------------------------------------------------

data VarReplace
  = VarReplace Dej Term

renderVarReplace :: GammaNames -> VarReplace -> Doc AnsiStyle
renderVarReplace gamma (VarReplace dej tm) =
  renderVar gamma dej <+> asymbol ":=" <+> renderTerm gamma tm

instance Weaken VarReplace where
  weaken lvl (VarReplace i tm) = VarReplace (weaken lvl i) (weaken lvl tm)

class ReplaceVar a where
  replaceVars :: [VarReplace] -> a -> a

instance ReplaceVar a => ReplaceVar (Param a) where
  replaceVars reps = fmap $ replaceVars reps

instance ReplaceVar Term where
  replaceVars reps (Var i) =
    case find (\(VarReplace i' tm) -> i == i') reps of
      Nothing                -> Var i
      Just (VarReplace _ tm) -> tm
  replaceVars reps (Bound n) = Bound n
  replaceVars reps (Alien x) = Alien x
  replaceVars reps (App f x) = App (replaceVars reps f) (replaceVars reps x)
  replaceVars reps (Lam n e) = Lam n (replaceVars (weakenBy n reps) e)
  replaceVars reps (Pi a b) = Pi (replaceVars reps a) (replaceVars (weakenBy a reps) b)
  replaceVars reps TType = TType
  replaceVars reps (Func n) = Func n
  replaceVars reps (Con c n) = Con c n
  replaceVars reps (Meta n) = Meta n
  replaceVars reps (Prim x) = Prim x
