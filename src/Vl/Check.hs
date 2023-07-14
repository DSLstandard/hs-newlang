module Vl.Check where

import Control.Algebra
import Control.Carrier.Error.Either qualified as C
import Control.Carrier.Lift qualified as C
import Control.Carrier.Reader qualified as C
import Control.Carrier.State.Strict qualified as C
import Control.Effect.Fresh qualified as C
import Control.Effect.Reader qualified as C
import Control.Effect.State qualified as C
import Control.Monad.Extra (fromMaybeM, mconcatMapM)

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set

import Error.Diagnose

import Prettyprinter
import Prettyprinter.Render.Terminal

import Relude

import Utils
import Utils.Pretty

import Vl.Algo
import Vl.Common
import Vl.Defs
import Vl.Error
import Vl.Expr
import Vl.Jesper
import Vl.Lens
import Vl.Name
import Vl.Parser (inPiInfo)
import Vl.TT
import Vl.Unify
import Vl.Value

import Witherable

data SearchSolution
  = SearchSolution
      { _newDefs :: Defs
        -- ^ updated defs
      , _term    :: Term
        -- ^ solution term under context
      }
makeFieldsNoPrefix ''SearchSolution

unknownVar :: HasError sig m => Range -> AmbigName -> m a
unknownVar range name = C.throwError @Error $ GenericReport
  $ simpleErr "Unknown variable"
    [ (toPos range, This $ "unknown variable '" <> show name <> "'")
    ]
    []

duplicateDef :: HasError sig m => Range -> QName -> m a
duplicateDef range name = C.throwError @Error $ GenericReport
  $ simpleErr "Duplicate definition"
    [ (toPos range, This $ "definition name '" <> show name <> "' has already been used")
    ]
    []

addNewDef :: (WithDefs sig m, HasError sig m) => Range -> QName -> Type' Term -> Def -> m ()
addNewDef range n t d = do
  defs <- currentDefs
  case defsLookup n defs of
    Nothing -> setDef n t d
    Just d' -> duplicateDef range n

resolveAmbigNameUniquely :: (GotNamespacing sig m, WithDefs sig m, HasError sig m)
  => Range -> AmbigName -> m (QName, DefInfo Def)
resolveAmbigNameUniquely namerange ambigname = do
  searchAmbigNameDef ambigname >>= \case
    [] -> do
      -- no resolution => bad
      unknownVar namerange ambigname
    [cand] -> do
      -- unique resolution => good
      pure cand
    ds -> do
      -- non-unique resolution => bad
      let cands = fmap fst $ ds
      C.throwError $ GenericReport $ Err Nothing "Ambiguous name"
        [ (toPos namerange, This $ "ambiguous name '" <> show ambigname <> "'")
        , (toPos namerange, Where $ "could refer to: " <> show (pretty cands))
        ]
        [ Hint "Use a more qualified name."
        ]

------------------------------------------------------------------------
-- * Fresh name
------------------------------------------------------------------------

freshName :: GenUUID sig m => Text -> m Name
freshName name = VirtName name <$> C.fresh

freshNameFrom :: GenUUID sig m => Name -> m Name
freshNameFrom = freshName . nameRoot

freshMetaName :: GenUUID sig m => Text -> m NewMetaName
freshMetaName name = NewMetaName . qnameSingleton . VirtName name <$> C.fresh

freshMetaNameFrom :: GenUUID sig m => Name -> m NewMetaName
freshMetaNameFrom = freshMetaName . nameRoot

------------------------------------------------------------------------
-- * ImplicitBind
------------------------------------------------------------------------

data ImplicitBind
  = ImplicitBind
      { _metaName  :: NewMetaName
      , _isBindVar :: Bool
        -- this
      , _piInfo    :: PiInfo
        -- ^ the pi info the name is bound to, this is mainly used for insres
      , _numArgs   :: Level
        -- ^ for replacing metas after binding implicits, FIXME: this is unholy
      , _term      :: Term
        -- ^ substitution term
      , _dtype     :: Type' Term
        -- ^ substitution term's type
      }
  deriving (Show)
makeFieldsNoPrefix ''ImplicitBind

renderImplicitBind :: GammaNames -> (Name, ImplicitBind) -> Doc AnsiStyle
renderImplicitBind gamma (name, ImplicitBind mn _ p _ tm ty) =
  renderPiInfo p (alocal (pretty name))
    <+> asymbol "~>" <+> renderTerm gamma tm <+> ":" <+> renderTerm gamma ty

------------------------------------------------------------------------
-- * CheckSt
------------------------------------------------------------------------

data CheckSt
  = CheckSt
      { _implicitBinds :: [(Name, ImplicitBind)]
      }
makeFieldsNoPrefix ''CheckSt

initCheckSt :: CheckSt
initCheckSt = CheckSt
  { _implicitBinds = []
  }

----- ============================================================ -----
-- ** CheckSt utilities
----- ============================================================ -----

registerImplicitBind :: Has (C.State CheckSt) sig m => Name -> ImplicitBind -> m ()
registerImplicitBind name bind = C.modify @CheckSt $ implicitBinds %~ ((name, bind) :)

------------------------------------------------------------------------
-- * CheckMode
------------------------------------------------------------------------

data CheckMode
  = CheckModeLHS
  | CheckModeExpr
  deriving (Eq, Show)

----- ============================================================ -----
-- ** CheckMode utilities
----- ============================================================ -----

isInLHS :: Has (C.Reader CheckMode) sig m => m Bool
isInLHS = C.asks @CheckMode (== CheckModeLHS)

------------------------------------------------------------------------
-- * Check
------------------------------------------------------------------------

type HasCheck sig m =
  ( Has (C.Lift IO) sig m
  , GenUUID sig m
  , HasError sig m
  , WithDefs sig m
  , GotContext sig m
  , GotNamespacing sig m
  , Has (C.Reader CheckMode) sig m
  , Has (C.State CheckSt) sig m
  )

------------------------------------------------------------------------
-- * ExpectType
------------------------------------------------------------------------

data ExpectType' a
  = Infer
  | Expect a
  deriving (Foldable, Functor, Traversable)

type ExpectType = ExpectType' Term

instance Weaken a => Weaken (ExpectType' a) where
  weaken lvl = fmap $ weaken lvl
instance WeakenAfter a => WeakenAfter (ExpectType' a) where
  weakenAfter off lvl = fmap $ weakenAfter off lvl

fromExpectType :: HasCheck sig m => Text -> ExpectType -> m Term
fromExpectType holename (Expect ty) = pure ty
fromExpectType holename Infer = do
  mn <- freshMetaName "CASERTY"
  newHole mn TType

------------------------------------------------------------------------
-- * Hooked
------------------------------------------------------------------------

noteSolutions :: (Has (C.Lift IO) sig m, WithDefs sig m) => USolutions -> m ()
noteSolutions sols = do
  when (solutionsExists sols) do
    C.sendIO $ putDocLn $ aspecial "solutions:" <+> list (fmap renderUSolution (Map.toList sols))
  defsSetSolutions sols

noteUResult :: (HasError sig m, GenUUID sig m, Has (C.Lift IO) sig m, WithDefs sig m)
  => UResult -> m [UnifyConstraint]
noteUResult (UResult sols cs) = do
  noteSolutions sols
  if solutionsExists sols then do
    reviseAllGuesses
    noteUResult =<< defsReviseUnifyConstraints cs
  else do
    pure cs

attachConstraintsTo ::
  ( Has (C.Lift IO) sig m
  , WithDefs sig m
  , GotContext sig m
  , GenUUID sig m
  )
  => Term
  -> Type' Term
  -> [UnifyConstraint]
  -> m Term
attachConstraintsTo tm ty cs = do
  case nonEmpty cs of
    Nothing -> pure tm
    Just cs -> newBlocked tm ty cs

------------------------------------------------------------------------
-- * TypeChecking logic
------------------------------------------------------------------------

typeCheck :: HasCheck sig m => Term -> Range -> Type' Term -> ExpectType -> m (Term, Type' Term)
typeCheck tm tmrange ty Infer = pure (tm, ty)
typeCheck tm tmrange usrty (Expect expty) = do
  -- do
  --   gamma <- contextGammaNames <$> currentContext
  --   C.sendIO $ putDocLn $ "checking:" <+> renderTerm gamma ty <+> "~" <+> renderTerm gamma expty
  -- dont use mustConvert so as to make the error more sensible
  usrtynf <- defsEval usrty
  exptynf <- defsEval expty
  tycs <- noteUResult =<< uponInconsistency reportError (defsUnify usrtynf exptynf)
  tm <- attachConstraintsTo tm expty tycs
  pure (tm, expty)
  -- C.sendIO $ putDocLn $ "typeCheck @ " <> pretty tmrange
  --   <> " got constraints: " <> list (fmap renderUnifyConstraint (toList tycs))
  where
  reportError = do
    gamma <- contextGammaNames <$> currentContext
    tm <- defsNormWith optsReduceMetas tm
    usrty <- defsNormWith optsReduceAll usrty
    expty <- defsNormWith optsReduceAll expty
    C.throwError @Error $ GenericReport
      $ simpleErr "Typecheck failed"
        [ (toPos tmrange, This $ show $ "got type:" <+> renderTerm gamma usrty)
        , (toPos tmrange, This $ show $ "but want:" <+> renderTerm gamma expty)
        , (toPos tmrange, Where $ show $ "term:" <+> renderTerm gamma tm)
        ]
        []

checkTypeExpr :: HasCheck sig m => Type' Expr -> m (Type' Term)
checkTypeExpr ty = fst <$> checkExpr ty (Expect TType)

checkParam :: HasCheck sig m => EParam -> m (Param Term)
checkParam (EParam range piinfo name namerange argty) = do
  argty <- checkTypeExpr argty
  pure $ Param piinfo name argty

checkLam :: HasCheck sig m => Range -> EParam -> Expr -> ExpectType -> m (Term, Type' Term)
checkLam range param body Infer = do
  param <- checkParam param
  (body, bodyty) <- underParam param $ checkExpr body Infer
  pure (Lam (param^.name) body, Pi param bodyty)
checkLam range param body (Expect exp) = do
  param <- checkParam param
  defsNormWith optsReduceAll exp >>= \case
    Pi sysparam sysbodyty -> do
      paramcs <- do
        -- do this or else stuff like `the (Type -> Type) (\(x : String) -> Type)` will be accepted
        --   because it would not check if `Type ~ String`
        argtynf    <- defsEval (param^.argType)
        sysargtynf <- defsEval (sysparam^.argType)
        noteConvert argtynf sysargtynf
      (body, bodyty) <- underParam param $ checkExpr body (Expect sysbodyty)
      let tm = Lam (param^.name) body
      let ty = Pi param bodyty
      tm <- attachConstraintsTo tm ty paramcs
      pure (tm, ty)
    exp -> do
      (body, bodyty) <- underParam param $ checkExpr body Infer
      typeCheck (Lam (param^.name) body) range (Pi param bodyty) (Expect exp)
-- simpler implementation: but spawns more constraints as retty is FIRST inferred, THEN checked
-- checkLam range param scope exp = do
--   param <- checkParam param
--   (scope, retty) <- underParam param $ checkExpr scope Infer
--   typeCheck (Lam (param^.name) scope) range (Pi param retty) exp


checkPi :: HasCheck sig m => Range -> EParam -> Expr -> ExpectType -> m (Term, Type' Term)
checkPi range param retty exp = do
  param <- checkParam param
  retty <- underParam param $ checkTypeExpr retty
  typeCheck (Pi param retty) range TType exp


checkHole :: HasCheck sig m => Range -> ExpectType -> m (Term, Type' Term)
checkHole range exp = do
  ty <- fromExpectType "HTY" exp
  mn <- freshMetaName "HOL"
  C.sendIO $ putDocLn $ "created" <+> ameta (pretty mn) <+> "@" <+> pretty range
  tm <- newHole mn ty
  pure (tm, ty)


checkExpr :: HasCheck sig m => Expr -> ExpectType -> m (Term, Type' Term)
checkExpr expr@EVar{} exp =
  checkAppStart expr [] exp
checkExpr expr@EResolvedVar{} exp =
  checkAppStart expr [] exp
checkExpr expr@EApp{} exp =
  checkAppStart expr [] exp
checkExpr (EType range) exp = do
  typeCheck TType range TType exp
checkExpr (EPi range param retty) exp = do
  checkPi range param retty exp
checkExpr (ELam range param scope) exp = do
  checkLam range param scope exp
checkExpr (EUserHole range name) exp = do
  checkUserHole range name exp
checkExpr (EPrim range prim) exp = do
  checkPrim range prim exp
checkExpr (ECase casebase) exp = do
  checkCaseBase casebase exp
checkExpr (ELet casebase) exp = do
  checkCaseBase casebase exp
checkExpr (EHole range) exp = do
  checkHole range exp
checkExpr expr@EOpTree{} exp = do
  expr <- checkFixity expr
  checkExpr expr exp


checkAmbigVar :: HasCheck sig m => Range -> AmbigName -> ExpectType -> m (Term, Type' Term)
checkAmbigVar range ambigname exp = do
  tryAllOrElse
    (unknownVar range ambigname)
    [asLocal, asGlobal, asBindVar]
  where
  mustBeSingle = hoistMaybe $ ambigNameSingle ambigname

  asLocal = do
    varname <- mustBeSingle
    ctx <- currentContext
    [(dej, param)] <- pure $ contextLookupBy (== varname) ctx
    let tm = Var dej
    let ty = param^.argType
    typeCheck tm range ty exp

  asGlobal = do
    [(qname, d)] <- searchAmbigNameDef ambigname
    let tm = referDef (d^.info) qname
    let ty = d^.dtype
    typeCheck tm range ty exp

  asBindVar = do
    guardM isInLHS
    varname <- mustBeSingle
    checkBindVar range varname exp


checkAppStart :: HasCheck sig m => Expr -> [AppArg EArg] -> ExpectType -> m (Term, Type' Term)
checkAppStart (EApp apprange fn arg) args exp =
  checkAppStart fn (AppArg apprange arg : args) exp

checkAppStart (EResolvedVar varrange qname) args exp = do
  d <- lookupDefSured qname
  let var = referDef (d^.info) qname
  vartynf <- defsEval (d^.dtype)
  checkApp vartynf var varrange args exp

checkAppStart (EVar varrange ambigname) args exp = do
  (var, varty) <- checkAmbigVar varrange ambigname Infer
  vartynf <- defsEval varty
  checkApp vartynf var varrange args exp

checkAppStart fnexpr args exp = do
  (fn, fnty) <- checkExpr fnexpr Infer
  fnty <- defsEval fnty
  checkApp fnty fn (exprRange fnexpr) args exp


checkApp :: HasCheck sig m => Type' NF -> Term -> Range -> [AppArg EArg] -> ExpectType -> m (Term, Type' Term)
checkApp
  (NPi (Param Explicit _ argtynf) apptynf)
  fn fnrange (AppArg apprange (EArg argrange TheExplicit arg) : args) exp = do
    -- auto-generate user-written apply explicit arg
    (arg, argty) <- checkExpr arg (Expect (quotate argtynf))
    argnf <- defsEval arg
    checkApp (runScope apptynf argnf) (App fn arg) apprange args exp
checkApp
  (NPi (Param (Implicit imp) _ argtynf) apptynf)
  fn fnrange (AppArg apprange (EArg argrange TheImplicit arg) : args) exp = do
    -- auto-generate user-written apply implicit arg
    (arg, argty) <- checkExpr arg (Expect (quotate argtynf))
    argnf <- defsEval arg
    checkApp (runScope apptynf argnf) (App fn arg) apprange args exp
checkApp
  (NPi (Param (Implicit imp) argn argtynf) appty)
  fn fnrange args exp = do
    -- auto-generate implicit arg holes
    arg <- implicitArg imp argn (quotate argtynf)
    argnf <- defsEval arg
    checkApp (runScope appty argnf) (App fn arg) fnrange args exp
checkApp fntynf fn fnrange (AppArg apprange (EArg argrange plicity arg) : args) exp = do
  -- make up `fnty ~ ?a -> ?b`
  (arg, argty) <- checkExpr arg Infer
  retty <- do
    mn <- freshMetaName "RETTY"
    newHole mn TType
  let
    piinfo = case plicity of
      TheExplicit -> Explicit
      TheImplicit -> Implicit IsImplicit
    param = Param piinfo boringName argty
    sysfnty :: Term = Pi param (weaken 1 retty)
  sysfntynf <- defsEval sysfnty
  do
    gamma <- contextGammaNames <$> currentContext
    fnty <- defsNormWith optsReduceMetas (quotate fntynf)
    sysfnty <- defsNormWith optsReduceMetas (quotate sysfntynf)
    C.sendIO $ putDocLn $ aspecial "checkApp inventing fnty:" <+> renderTerm gamma fnty <+> asymbol "~" <+> renderTerm gamma sysfnty
  fncs <- uponInconsistency
    ( do
      C.throwError $ GenericReport $ Err Nothing "Bad function type"
        [ (toPos fnrange, This "bad function type")
        ]
        []
    )
    (noteConvert fntynf sysfntynf)
  -- fn <- case nonEmpty fncs of
  --   Nothing -> pure fn
  --   Just fncs -> do
  --     C.sendIO $ putDocLn $ "checkApp @ " <> pretty fnrange <>
  --       " got constraints: " <> list (fmap renderUnifyConstraint (toList fncs))
  --     newBlocked fn (quotate systemfntynf) fncs
  fn <- attachConstraintsTo fn sysfnty fncs
  rettynf <- defsEval retty
  checkApp rettynf (App fn arg) apprange args exp
checkApp fnty fn fnrange [] exp =
  -- no more arguments => finish!!!!!!
  typeCheck fn fnrange (quotate fnty) exp

implicitArg :: HasCheck sig m => ImplicitInfo -> Name -> Type' Term -> m Term
implicitArg imp argname argty = do
  ifM isInLHS
    ( do -- in LHS
      -- add an implicit bind
      mn <- freshMetaNameFrom argname
      arg <- newHole mn argty
      lvl <- length <$> currentContext
      registerImplicitBind argname (ImplicitBind mn False (Implicit imp) lvl arg argty)
      pure arg
    )
    ( do -- not in LHS
      newImplicitArgHole imp argname argty
    )

checkCaseBase :: HasCheck sig m => ECaseBase -> ExpectType -> m (Term, Type' Term)
checkCaseBase ECaseBase{..} exp = do
  (scr, scrty) <- checkExpr _scrutinee Infer

  -- do
  --   ctx <- currentContext
  --   let gamma = contextGammaNames ctx
  --   C.sendIO $ putDocLn $ "scrctx: " <> renderContext ctx
  --   scr <- withDefsNormalizeWith optsReduceMetas scr
  --   scrty <- withDefsNormalizeWith optsReduceMetas scrty
  --   C.sendIO $ putDocLn $ "scr: " <> renderTerm gamma scr <+> asymbol ":" <+> renderTerm gamma scrty

  retty <- fromExpectType "CASERTY" exp
  casename <- VirtName "case" <$> C.fresh
  caseqname <- makeQNameSingleton casename
  underScrutinee scrty do
    -- gamma <- contextGammaNames <$> currentContext
    scrty <- pure $ weaken 1 scrty
    retty <- pure $ weaken 1 retty
    -- C.sendIO $ putDocLn $ "updated retty:" <+> renderTerm gamma retty
    clauses <- traverse (checkClause (Expect scrty) (ClauseModeCase (Expect retty))) _clauses
    -- for_ clauses \clause -> do
    --   C.sendIO $ putDocLn $ "got clause:" <+> renderUserClause gamma clause
    tree <- buildCaseTree _range clauses
    ctx <- currentContext
    let argnames = reverse (contextGammaNames ctx)
    let casety :: Closed Term = abstractPis retty ctx
    let casepm = PatternFunc argnames tree
    -- C.sendIO $ putDocLn $ "casety:" <+> renderTerm [] casety
    -- C.sendIO $ putDocLn $ "casepm:" <+> renderPatternFunc casefnname casepm
    addNewDef _range caseqname casety (DefPM casepm)
  ctx <- currentContext
  let casetm = App (foldSpine (Func caseqname) (constArgs (length ctx))) scr
  pure (casetm, retty)

checkUserHole :: HasCheck sig m => Range -> Name -> ExpectType -> m (Term, Type' Term)
checkUserHole range name exp = do
  localty <- fromExpectType (nameRoot name <> "ty") exp
  ctx <- currentContext
  let qname = qnameSingleton name
  addNewDef range qname (abstractPis localty ctx) DefUserHole
  pure (foldSpine (Func qname) (constArgs (length ctx)), localty)

checkPrim :: HasCheck sig m => Range -> Primitive -> ExpectType -> m (Term, Type' Term)
checkPrim range prim exp = do
  typeCheck (Prim prim) range (typeOfPrim prim) exp

checkBindVar :: HasCheck sig m => Range -> Name -> ExpectType -> m (Term, Type' Term)
checkBindVar range varname exp = do
  binds <- C.gets @CheckSt $ view implicitBinds
  case List.lookup varname binds of
    Nothing -> do
      ty <- fromExpectType "HTY" exp
      bindmn <- freshMetaNameFrom varname
      tm <- newHole bindmn ty
      lvl <- length <$> currentContext
      registerImplicitBind varname (ImplicitBind bindmn True Explicit lvl tm ty)
      pure (tm, ty)
    Just bind -> do
      typeCheck (bind^.term) range (bind^.dtype) exp

checkBindHere :: forall sig m. HasCheck sig m => Expr -> ExpectType -> m (SubContext, Term, Type' Term)
checkBindHere expr exp = do
  oldbinds <- C.gets @CheckSt $ view implicitBinds -- restore
  C.modify @CheckSt $ implicitBinds .~ [] -- isolate
  (tm, ty) <- checkExpr expr exp
  do
    gamma <- contextGammaNames <$> currentContext
    -- C.sendIO $ putDocLn $ "checkBindHere:" <+> list (renderImplicitBind gamma <$> binds)
    C.sendIO $ putDocLn $ "checkBindHere before: " <> (renderTerm gamma tm <+> asymbol ":" <+> renderTerm gamma ty)
    tm <- defsNormWith optsReduceMetas tm
    ty <- defsNormWith optsReduceMetas ty
    C.sendIO $ putDocLn $ "checkBindHere after:  " <> (renderTerm gamma tm <+> asymbol ":" <+> renderTerm gamma ty)
  binds <- C.gets @CheckSt $ view implicitBinds
  C.modify @CheckSt $ implicitBinds .~ oldbinds -- save

  binds <- filterM shouldBind binds
  binds <- traverse normalizeBind binds
  binds <- pure $ sortByDependency binds
  tm <- defsNormWith optsReduceMetas tm
  ty <- defsNormWith optsReduceMetas ty
  -- gamma <- contextGammaNames <$> currentContext
  -- C.sendIO $ putDocLn $ "checkBindHere:" <+> list (renderImplicitBind gamma <$> binds)
  -- C.sendIO $ putDocLn $ "checkBindHere:" <+> (renderTerm gamma tm <+> asymbol ":" <+> renderTerm gamma ty)
  underBinds [] binds do
    patctx <- contextSub (length binds) <$> currentContext
    let tm' = updateTerm (reverse binds) tm
    let ty' = updateTerm (reverse binds) ty
    tm' <- defsNormWith optsReduceMetas tm'
    ty' <- defsNormWith optsReduceMetas ty'
    -- C.sendIO $ putDocLn $ renderContext ctx
    -- C.sendIO $ putDocLn $ renderTerm (contextGammaNames ctx) tm <+> asymbol ":" <+> renderTerm (contextGammaNames ctx) ty
    -- C.sendIO $ putDocLn $ renderTerm (contextGammaNames ctx) tm' <+> asymbol ":" <+> renderTerm (contextGammaNames ctx) ty'
    pure (patctx, tm', ty')
  where
  -- weaken all dejs & replace metas
  updateTerm :: [(Name, ImplicitBind)] -> Term -> Term
  updateTerm binds = replace 0
    where
    replace off TType = TType
    replace off (Bound n) = Bound n
    replace off (Func n) = Func n
    replace off (Alien x) = Alien x
    replace off (Con c n) = Con c n
    replace off (Prim x) = Prim x
    replace off (Var dej) = Var (weakenAfter off (length binds) dej)
    replace off (App fn arg) = App (replace off fn) (replace off arg)
    replace off (Lam n scope) =
      Lam n (replace (off + 1) scope)
    replace off (Pi param scope) =
      Pi (replace off <$> param) (replace (off + 1) scope)
    replace off (Meta n) =
      case findWithIndex (\(_, bind) -> bind^.metaName.to unNewMetaName == n) binds of
        Nothing               -> Meta n
        Just (dej, (_, bind)) -> lams (bind^.numArgs) (Var ((bind^.numArgs) + dej + off))

  normalizeBind :: (Name, ImplicitBind) -> m (Name, ImplicitBind)
  normalizeBind (n, ImplicitBind mn isbindvar piinfo lvl tm ty) = do
    ty <- defsNormWith optsReduceAll ty
    pure (n, ImplicitBind mn isbindvar piinfo lvl tm ty)

  shouldBind :: (Name, ImplicitBind) -> m Bool
  shouldBind (_, ImplicitBind (NewMetaName mn) isbindvar piinfo lvl _ _) =
    not <$> isMetaSolved mn -- only bind unsolved metas

  -- analogous to Idris2's depSort
  sortByDependency :: [(Name, ImplicitBind)] -> [(Name, ImplicitBind)]
  sortByDependency binds = reverse $ fmap (view value) $ topologicalSortByDfs $
    (fmap (\bind -> Node (getKey bind) (getDepMetas bind) bind) binds)
    where
    getKey :: (Name, ImplicitBind) -> QName
    getKey (_, bind) = bind^.metaName.to unNewMetaName

    getDepMetas :: (Name, ImplicitBind) -> Set.Set QName
    getDepMetas (_, bind) = collectMetas (bind^.dtype)

  underBinds :: [(Name, ImplicitBind)] -> [(Name, ImplicitBind)] -> m a -> m a
  underBinds acc [] act = act
  underBinds acc ((name, bind) : rest) act = do
    name <- if bind^.isBindVar
      then pure name
      else freshNameFrom name
    let param = Param (bind^.piInfo) name $ updateTerm acc (bind^.dtype)
    underParam param $ underBinds ((name, bind) : acc) rest act


data ClauseMode
  -- | used for `case ... of ...` syntax
  = ClauseModeCase
      { _expectType :: ExpectType
      }
  -- | used for `plus (S x) y = ...` syntax
  | ClauseModePM

checkClause :: HasCheck sig m => ExpectType -> ClauseMode -> EClause -> m UserClause
checkClause lhsexp mode (EClause range elhs rhs) = do
  (patctx, lhs, lhsty) <- C.local (const CheckModeLHS) $ checkBindHere elhs lhsexp
  -- ctx <- currentContext
  -- C.sendIO $ putDocLn $ "fullctx =" <+> renderContext ctx
  extendContext patctx do
    -- ctx <- currentContext
    -- let gamma = contextGammaNames ctx
    -- C.sendIO $ putDocLn $ "patctx =" <+> renderContext patctx
    -- C.sendIO $ putDocLn $ "LHS =" <+> renderTerm gamma lhs
    -- C.sendIO $ putDocLn $ "LHSraw =" <+> show elhs
    case mode of
      ClauseModeCase rhsexp -> do
        (rhs, rhsty) <- checkExpr rhs (weaken (length patctx) rhsexp)
        pure (UserClause range patctx lhs rhs)
      ClauseModePM -> do
        -- let gamma = contextGammaNames ctx
        -- C.sendIO $ putDocLn $ renderContext ctx
        -- C.sendIO $ putDocLn $ renderTerm gamma lhs <+> asymbol ":" <+> renderTerm gamma lhsty
        -- C.sendIO $ putDocLn $ renderTerm gamma lhs <+> asymbol "=" <+> renderTerm gamma rhs
        (rhs, lhsty) <- checkExpr rhs (Expect lhsty)
        pure (UserClause range patctx lhs rhs)

------------------------------------------------------------------------
-- * Fixity
------------------------------------------------------------------------

data OpTree
  = OpNode
      { _left        :: OpTree
      , _opName      :: QName
      , _opInfo      :: OpInfo
      , _opNameRange :: Range
      , _right       :: OpTree
      }
  | OpLeaf Expr

opTreePrepend :: forall sig m. (GotNamespacing sig m, HasError sig m, WithDefs sig m)
  => Expr -> QName -> OpInfo -> Range -> OpTree -> m OpTree
opTreePrepend larg lop lo loprange (OpLeaf rarg) = do
  pure $ OpNode (OpLeaf larg) lop lo loprange (OpLeaf rarg)
opTreePrepend larg lop lo loprange (OpNode rltree rop ro roprange rrtree) = do
  let
    assocLeft :: m OpTree
    assocLeft = do
      rltree <- opTreePrepend larg lop lo loprange rltree
      pure $ OpNode rltree rop ro roprange rrtree

    assocRight :: m OpTree
    assocRight = do
      pure $ OpNode (OpLeaf larg) lop lo loprange (OpNode rltree rop ro roprange rrtree)

  if lop == rop then do
    case lo^.fixity of
      Infix  -> C.throwError $ GenericReport $ Err Nothing "Operator precedence error"
        [ (toPos loprange, This $ "cannot mix multiple '" <> showOp lop lo <> "' in the same infix expression")
        , (toPos roprange, Where $ "clashed with this")
        ]
        []
      Infixl -> assocLeft
      Infixr -> assocRight
  else do
    case compare (lo^.precedence) (ro^.precedence) of
      EQ -> undefined
      GT -> assocLeft
      LT -> assocRight
  where
  showOp :: QName -> OpInfo -> Text
  showOp op info = show op <> " [" <> show info <> "]"


opTreeToExpr :: OpTree -> Expr
opTreeToExpr (OpLeaf expr) = expr
opTreeToExpr (OpNode left op opinfo oprange right) = do
  let left' = opTreeToExpr left
  let right' = opTreeToExpr right
  let app1 = EResolvedVar oprange op
  let app2 = EApp (exprRange left' <> oprange) app1 (EArg (exprRange left') TheExplicit left')
  let app3 = EApp (exprRange left' <> oprange) app2 (EArg (exprRange right') TheExplicit right')
  app3


checkFixity :: (HasError sig m, GotNamespacing sig m, WithDefs sig m) => Expr -> m Expr
checkFixity = fmap opTreeToExpr . go
  where
  go (EOpTree leftarg opname opnamerange righttree) = do
    (opqname, d) <- resolveAmbigNameUniquely opnamerange opname
    opTreePrepend leftarg opqname (d^.opInfo) opnamerange =<< go righttree
  go expr = pure $ OpLeaf expr

------------------------------------------------------------------------
-- * Meta
------------------------------------------------------------------------

newHole :: (WithDefs sig m, GotContext sig m) => NewMetaName -> Type' Term -> m Term
newHole (NewMetaName mn) ty = do
  ctx <- currentContext
  let absty = abstractPis ty ctx
  setDef mn absty DefHole
  pure $ foldSpine (Meta mn) (constArgs (length ctx))


newBlocked :: (Has (C.Lift IO) sig m, GenUUID sig m, WithDefs sig m, GotContext sig m)
  => Term -> Type' Term -> NonEmpty UnifyConstraint -> m Term
newBlocked tm ty constraints = do
  ctx <- currentContext
  let absty = abstractPis ty ctx
  let abstm = lamsNamed (contextGammaNames ctx) tm
  NewMetaName mn <- freshMetaName "BLK"
  registerGuessName mn
  setDef mn absty $ DefBlocked Blocked
    { _term = abstm
    , _constraints = constraints
    }
  do
    let gamma = contextGammaNames ctx
    C.sendIO $ putDocLn $ aspecial "new blocked " <> ameta (pretty mn) <> ": " <> renderTerm gamma tm <+> asymbol ":" <+> renderTerm gamma ty
      <> ", constraints = " <> list (fmap renderUnifyConstraint (toList constraints))
  pure $ foldSpine (Meta mn) (constArgs (length ctx))


newSearch :: (Has (C.Lift IO) sig m, GenUUID sig m, WithDefs sig m, GotContext sig m)
  => NewMetaName -> Type' Term -> m Term
newSearch (NewMetaName mn) ty = do
  ctx <- currentContext
  let absty = abstractPis ty ctx
  hints <- C.gets @Defs $ view searchHints
  setDef mn absty $ DefSearch Search
    { _hints = hints
    }
  registerGuessName mn
  pure $ foldSpine (Meta mn) (constArgs (length ctx))


newImplicitArgHole :: (Has (C.Lift IO) sig m, HasError sig m, GenUUID sig m, WithDefs sig m, GotContext sig m)
  => ImplicitInfo -> Name -> Type' Term -> m Term
newImplicitArgHole imp argname argty = do
  case imp of
    IsImplicit -> do
      mn <- freshMetaNameFrom argname
      newHole mn argty
    IsInstance -> do
      defs <- C.get @Defs
      NewMetaName mn <- freshMetaNameFrom argname
      tm <- newSearch (NewMetaName mn) argty
      -- attempt to solve it immediately
      progress <- reviseSearch mn
      when (getAny progress) (void reviseAllGuesses)
      pure tm


newSearchArgHole :: (Has (C.Lift IO) sig m, HasError sig m, GenUUID sig m, WithDefs sig m, GotContext sig m)
  => ImplicitInfo -> Name -> Type' Term -> m Term
newSearchArgHole imp argname argty = do
  case imp of
    IsImplicit -> do
      mn <- freshMetaNameFrom argname
      newHole mn argty
    IsInstance -> do
      defs <- C.get @Defs
      NewMetaName mn <- freshMetaNameFrom argname
      newSearch (NewMetaName mn) argty

------------------------------------------------------------------------
-- * Solution
------------------------------------------------------------------------

type Progress = Any

reviseBlocked :: (Has (C.Lift IO) sig m, HasError sig m, WithDefs sig m)
  => QName -> m Progress
reviseBlocked n = do
  blocked <- lookupDefSuredAs _DefBlocked n
  UResult sols cs <- C.runReader emptyContext $ defsReviseUnifyConstraints (toList (blocked^.info.constraints))
  noteSolutions sols
  case nonEmpty cs of
    Nothing -> do
      -- all constraints blocking the term has been discharged => solved
      updateHoleToSolution n (blocked^.info.term)
      deregisterGuessName n
      C.sendIO $ putDocLn $ aspecial "solved blocked:" <+> ameta (pretty n)
      pure (Any True)
    Just cs -> do
      setDefInfo n blocked
        { _info = DefBlocked (blocked^.info)
          { _constraints = cs
          }
        }
      pure (Any (solutionsExists sols))


reviseAllGuesses :: (Has (C.Lift IO) sig m, GenUUID sig m, HasError sig m, WithDefs sig m)
  => m ()
reviseAllGuesses = do
  guessnames <- C.gets @Defs $ view guessNames
  C.sendIO $ putDocLn $ annotate (color Cyan <> underlined) "reviseAllGuesses invoked:" <+> list (fmap (ameta . pretty) (Set.toList $ guessnames))
  progress <- flip mconcatMapM (Set.toList guessnames) \guessname -> do
    guess <- lookupDefSured guessname
    case guess^.info of
      DefBlocked{} -> reviseBlocked guessname
      DefSearch{}  -> reviseSearch guessname
      _            -> pure mempty -- a guess might be solved after checking preceding guesses, simply do nothing when this is the case
  if getAny progress
    then reviseAllGuesses
    else C.sendIO $ putDocLn $ aspecial "reviseAllGuesses finished"


noteConvert :: (GotContext sig m, GenUUID sig m, HasError sig m, WithDefs sig m, Has (C.Lift IO) sig m)
  => NF -- ^ user written
  -> NF -- ^ system generated
  -> m [UnifyConstraint]
noteConvert usernf systemnf = do
  noteUResult =<< defsUnify usernf systemnf

------------------------------------------------------------------------
-- * Searching
------------------------------------------------------------------------

searchType :: (Has (C.Lift IO) sig m, GotContext sig m, GenUUID sig m, HasError sig m, WithDefs sig m)
  => Type' Term -- ^ local type
  -> SearchHints -- ^ hints
  -> m ()
searchType searchty hints = do
  underTelescope searchty \delta goalty -> do
    -- goaltynf <- defsEval goalty
    -- initcands <- getCandidates hints
    undefined
  where
  saturateArgs :: (HasError sig m, Has (C.Lift IO) sig m, GenUUID sig m, WithDefs sig m, GotContext sig m)
    => Term -> Type' NF -> m ([Term], Term, Type' NF)
  saturateArgs tm (NPi param nextty) = do
    let
      argty = quotate (param^.argType)
      impinfo = case param^.piInfo of
        Explicit     -> IsImplicit
        Implicit imp -> imp
    arg <- newSearchArgHole impinfo (param^.name) argty
    argnf <- defsEval arg
    (newargs, finaltm, finalty) <- saturateArgs (App tm arg) (runScope nextty argnf)
    pure (arg : newargs, finaltm, finalty)
  saturateArgs tm ty = pure ([], tm, ty)

  searchValidLocal :: (GotContext sig m, WithDefs sig m) => Type' NF -> m [(Term, Type' Term)]
  searchValidLocal goaltynf = do
    cands <- getLocalCandidates
    undefined

  getCandidates :: (GotContext sig m, WithDefs sig m) => m [(Term, Type' Term)]
  getCandidates = do
    locals <- getLocalCandidates
    globals <- getGlobalCandidates
    pure $ locals <> globals

  getLocalCandidates :: (GotContext sig m, WithDefs sig m) => m [(Term, Type' Term)]
  getLocalCandidates = do
    params <- contextFlatten <$> currentContext
    pure $ flip Witherable.mapMaybe params \(dej, param) -> do
      guard $ param^.piInfo == Implicit IsInstance
      pure (Var dej, param^.argType)

  getGlobalCandidates :: WithDefs sig m => m [(Term, Type' Term)]
  getGlobalCandidates = do
    forM (hints^.instances) \candname -> do
      cand <- lookupDefSured candname
      pure (referDef (cand^.info) candname, cand^.dtype)


reviseSearch :: (Has (C.Lift IO) sig m, GenUUID sig m, HasError sig m, WithDefs sig m)
  => QName -> m Progress
reviseSearch n = do
  C.sendIO $ putDocLn $ aspecial "reviseSearch: " <> ameta (pretty n)
  search <- lookupDefSuredAs _DefSearch n
  searchty <- defsNormWith optsReduceAll (search^.dtype)
  C.runReader emptyContext $ underTelescope searchty \gamma goalty -> do
    goaltynf <- defsEval goalty
    initcands <- getCandidates (search^.info)
    originaldefs <- C.get @Defs -- save
    results <- forMaybe initcands \(initcandtm, initcandty) -> do
      C.put originaldefs
      candtynf <- defsEval initcandty
      (candtm, candtynf) <- saturateArgs initcandtm candtynf
      do -- tracing
        gamma <- contextGammaNames <$> currentContext
        candtm <- defsNormWith optsReduceMetas candtm
        candty <- defsNormWith optsReduceMetas (quotate candtynf)
        C.sendIO $ putDocLn $
          "reviseSearch:" <+> ameta (pretty n) <+> "..."
            <+> renderTerm gamma candtm <+> asymbol ":"
            <+> renderTerm gamma candty <+> asymbol "~>" <+> renderTerm gamma goalty
      uponInconsistency
        ( do
            C.sendIO $ putDocLn $
              "reviseSearch discard candidate:" <+> ameta (pretty n) <+> "..."
                <+> renderTerm gamma candtm <+> asymbol ":"
                <+> renderTerm gamma initcandty <+> asymbol "~>" <+> renderTerm gamma goalty
            pure Nothing
        )
        ( do
            let abscandtm = lamsNamed gamma candtm
            UResult matchsols matchcs <- defsUnify candtynf goaltynf -- DO NOT ACCIDENTALLY USE mustConvert
            noteSolutions matchsols
            unless (null matchcs) do
              -- Idris2's searchName
              C.throwError $ Inconsistent "cannot unify with goalty without creating constraints" callStack
            updateDef n $ info .~ DefPM (fromSolution abscandtm)
            deregisterGuessName n
            C.sendIO $ putDocLn $ aspecial "REVISING ALL GUESSES UNDER SEARCH"
            revisesols <- reviseAllGuesses
            C.sendIO $ putDocLn $ aspecial "DONE!!!!!!! REVISING ALL GUESSES UNDER SEARCH"
            C.sendIO $ putDocLn $
              annotate (color Green) "reviseSearch accepting candidate:" <+> ameta (pretty n) <+> "..."
                <+> renderTerm gamma candtm <+> asymbol ":"
                <+> renderTerm gamma initcandty <+> asymbol "~>" <+> renderTerm gamma goalty
            defs <- C.get @Defs
            pure $ Just (SearchSolution defs candtm)
            -- FIXME: causes infinite, consider `Maybe_Show ?ins : Show (Maybe a) ~ Show ?m` without knowing what ?m is
            -- let abscandtm = lamsNamed gamma candtm
            -- UResult matchsols matchcs <- withDefsUnify candtynf goaltynf -- DO NOT ACCIDENTALLY USE mustConvert
            -- setSolutions matchsols
            -- case nonEmpty matchcs of
            --   Nothing -> do
            --     updateDef n $ info .~ DefPM (fromSolution abscandtm)
            --     deregisterGuessName n
            --   Just matchcs -> do
            --     updateDef n $ info .~ DefBlocked Blocked
            --       { _term = abscandtm
            --       , _constraints = matchcs
            --       }
            -- C.sendIO $ putDocLn $ aspecial "REVISING ALL GUESSES UNDER SEARCH"
            -- revisesols <- reviseAllGuesses
            -- C.sendIO $ putDocLn $ aspecial "DONE!!!!!!! REVISING ALL GUESSES UNDER SEARCH"
            -- C.sendIO $ putDocLn $
            --   annotate (color Green) "reviseSearch accepting candidate:" <+> ameta (pretty n) <+> "..."
            --     <+> renderTerm gamma candtm <+> asymbol ":"
            --     <+> renderTerm gamma initcandty <+> asymbol "~>" <+> renderTerm gamma goalty
            -- defs <- C.get @Defs
            -- pure $ Just (SearchSolution defs candtm)
        )
    C.put @Defs originaldefs -- restore
    case nonEmpty results of
      Nothing -> do
        C.sendIO $ putDocLn $ aspecial "no solutions found for" <+> ameta (pretty n)
        C.throwError $ Inconsistent "search has no solution" callStack
      Just allsols@(firstsol :| sols) -> do
        if allEqual allsols then do
          let SearchSolution newdefs candtm = firstsol
          C.put @Defs newdefs
          do
            candtm <- defsNormWith optsReduceMetas candtm
            C.sendIO $ putDocLn $ aspecial "set search" <+> ameta (pretty n) <+> "to" <+> renderTerm gamma candtm
          pure (Any True)
        else do
          canddocs <- forM (toList allsols) \(SearchSolution newdefs term) -> do
            term <- C.evalState newdefs $ defsNormWith optsReduceMetas term
            pure $ renderTerm gamma term
          C.sendIO $ putDocLn $ aspecial "yet to solve search" <+> ameta (pretty n) <+> "..." <+> list canddocs
          pure (Any False)
  where
  allEqual :: NonEmpty SearchSolution -> Bool
  allEqual (firstsol :| sols) = do
    let solnf = getNFOf firstsol
    all (convert solnf . getNFOf) sols
    where
    getNFOf :: SearchSolution -> NF
    getNFOf (SearchSolution newdefs term) = C.run $ C.evalState newdefs $ defsEval term

  getCandidates :: (GotContext sig m, WithDefs sig m) => Search -> m [(Term, Type' Term)]
  getCandidates search = do
    locals <- getLocalCandidates
    globals <- getGlobalCandidates search
    pure $ locals <> globals

  getLocalCandidates :: (GotContext sig m, WithDefs sig m) => m [(Term, Type' Term)]
  getLocalCandidates = do
    params <- contextFlatten <$> currentContext
    pure $ flip Witherable.mapMaybe params \(dej, param) -> do
      guard $ param^.piInfo == Implicit IsInstance
      pure (Var dej, param^.argType)

  getGlobalCandidates :: WithDefs sig m => Search -> m [(Term, Type' Term)]
  getGlobalCandidates search = do
    forM (search^.hints.instances) \candname -> do
      cand <- lookupDefSured candname
      pure (referDef (cand^.info) candname, cand^.dtype)

  saturateArgs :: (HasError sig m, Has (C.Lift IO) sig m, GenUUID sig m, WithDefs sig m, GotContext sig m)
    => Term -> Type' NF -> m (Term, Type' NF)
  saturateArgs tm (NPi param nextty) = do
    let
      argty = quotate (param^.argType)
      impinfo = case param^.piInfo of
        Explicit     -> IsImplicit
        Implicit imp -> imp
    arg <- newSearchArgHole impinfo (param^.name) argty
    argnf <- defsEval arg
    saturateArgs (App tm arg) (runScope nextty argnf)
  saturateArgs tm ty = pure (tm, ty)
