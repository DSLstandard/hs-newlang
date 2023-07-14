module Vl.Jesper where
import Control.Algebra
import Control.Carrier.Reader qualified as C
import Control.Carrier.State.Strict qualified as C
import Control.Carrier.Writer.Strict qualified as C
import Control.Effect.Error qualified as C
import Control.Effect.Lift qualified as C
import Control.Effect.Reader qualified as C
import Control.Effect.State qualified as C

import Data.List.Extra (mconcatMap)
import Data.Set qualified as Set

import Error.Diagnose

import Prettyprinter
import Prettyprinter.Render.Terminal

import Relude

import Utils (tryAllOrElse)
import Utils.Pretty

import Vl.Common
import Vl.Defs
import Vl.Error
import Vl.Expr
import Vl.Lens
import Vl.Name
import Vl.TT
import Vl.Value

import Witherable (forMaybe)

------------------------------------------------------------------------
-- * UserClause
------------------------------------------------------------------------

data UserClause
  = UserClause
      { _range      :: Range
      , _patContext :: SubContext
      , _lhs        :: Term
      , _rhs        :: Term
      }
makeFieldsNoPrefix ''UserClause

renderUserClause :: GammaNames -> UserClause -> Doc AnsiStyle
renderUserClause gamma clause =
  let gamma' = contextGammaNames (clause^.patContext) <> gamma
  in renderTerm gamma' (clause^.lhs) <+> asymbol "=>" <+> renderTerm gamma' (clause^.rhs)

------------------------------------------------------------------------
-- * Case stuff
------------------------------------------------------------------------

data CaseConstraint' a
  = CaseConstraint
      { _testPattern :: a
      , _userPattern :: a
      }
  deriving (Foldable, Functor, Traversable)
makeFieldsNoPrefix ''CaseConstraint'
type CaseConstraint = CaseConstraint' Term

data CaseClause' a
  = CaseClause
      { _constraints :: [CaseConstraint' a]
      , _rhs         :: a
      }
  deriving (Foldable, Functor, Traversable)
type CaseClause = CaseClause' Term
makeFieldsNoPrefix ''CaseClause'

data CaseProblem' a
  = CaseProblem
      { _testPattern :: a
      , _clauses     :: [CaseClause' a]
      }
  deriving (Foldable, Functor, Traversable)
type CaseProblem = CaseProblem' Term
makeFieldsNoPrefix ''CaseProblem'

instance Weaken a => Weaken (CaseConstraint' a) where
  weaken lvl = fmap (weaken lvl)

instance Weaken a => Weaken (CaseClause' a) where
  weaken lvl = fmap (weaken lvl)

instance Weaken a => Weaken (CaseProblem' a) where
  weaken lvl = fmap (weaken lvl)

instance ReplaceVar a => ReplaceVar (CaseConstraint' a) where
  replaceVars reps = fmap $ replaceVars reps

instance ReplaceVar a => ReplaceVar (CaseClause' a) where
  replaceVars reps = fmap $ replaceVars reps

instance ReplaceVar a => ReplaceVar (CaseProblem' a) where
  replaceVars reps = fmap $ replaceVars reps

instance ReplaceBound a => ReplaceBound (CaseConstraint' a) where
  replaceBounds reps = fmap $ replaceBounds reps

instance ReplaceBound a => ReplaceBound (CaseClause' a) where
  replaceBounds reps = fmap $ replaceBounds reps

instance ReplaceBound a => ReplaceBound (CaseProblem' a) where
  replaceBounds reps = fmap $ replaceBounds reps

renderCaseConstraint :: GammaNames -> CaseConstraint -> Doc AnsiStyle
renderCaseConstraint gamma (CaseConstraint test user) =
  renderTerm gamma test <+> asymbol "~" <+> renderTerm gamma user

renderCaseClause :: GammaNames -> CaseClause -> Doc AnsiStyle
renderCaseClause gamma CaseClause{..} =
  list (fmap (renderCaseConstraint gamma) _constraints) <+> asymbol "=>" <+> renderTerm gamma _rhs

renderCaseProblem :: GammaNames -> CaseProblem -> Doc AnsiStyle
renderCaseProblem gamma CaseProblem{..} = do
  nest 2 $ vsep
    ( renderTerm gamma _testPattern
    : fmap (renderCaseClause gamma) _clauses
    )

------------------------------------------------------------------------
-- * Unification for Jesper
------------------------------------------------------------------------

newtype JUnify a
  = JUnify { unJUnify :: StateT [CaseConstraint] Maybe a }
  deriving (Applicative, Functor, Monad)

runJUnify :: JUnify a -> Maybe ([CaseConstraint], a)
runJUnify = fmap swap . usingStateT [] . unJUnify

failJUnify :: JUnify a
failJUnify = JUnify empty

registerConstraint :: Term -> Term -> JUnify ()
registerConstraint lhs rhs = JUnify $ modify (CaseConstraint lhs rhs :)

junifySpine :: [Term] -> [Term] -> JUnify ()
junifySpine [] []             = pass
junifySpine (x : xs) (y : ys) = junify x y *> junifySpine xs ys
junifySpine _ _               = failJUnify

junify :: Term -> Term -> JUnify ()
junify lhs rhs = do
  case (unfoldSpine lhs, unfoldSpine rhs) of
    ((Con c1 n1, args1), (Con c2 n2, args2)) -> do
      unless (c1 == c2 && n1 == n2) failJUnify
      junifySpine args1 args2
    ((Var i1, []), (Var i2, [])) | i1 == i2 -> pass
    _ -> registerConstraint lhs rhs

junifyConstraint :: CaseConstraint -> JUnify ()
junifyConstraint (CaseConstraint lhs rhs) = junify lhs rhs

junifyWith :: forall a. Semigroup a
  => (CaseConstraint -> Maybe a)
  -> (a -> CaseConstraint -> CaseConstraint)
  -> [CaseConstraint]
  -> Maybe (Maybe a, [CaseConstraint])
junifyWith decide apply constraints = do
  (constraints, ()) <- runJUnify $ traverse_ junifyConstraint constraints
  (constraints, a) <- pure $ second mconcat $ partitionEithers $ fmap decide' $ constraints
  case a of
    Nothing -> pure (Nothing, constraints)
    Just a  -> first (Just a <>) <$> junifyWith decide apply constraints
  where
  decide' :: CaseConstraint -> Either CaseConstraint (Maybe a)
  decide' c = maybe (Left c) (Right . Just) (decide c)

------------------------------------------------------------------------
-- * Jesper
------------------------------------------------------------------------

type HasBuild sig m =
  ( WithDefs sig m
  , HasError sig m
  , GotContext sig m
  , Has (C.Lift IO) sig m
  )

data UnhandledPattern
  = UnhandledPattern
      { _context     :: Context
      , _userPattern :: Term
      }
makeFieldsNoPrefix ''UnhandledPattern

renderUnhandledPattern :: UnhandledPattern -> Doc AnsiStyle
renderUnhandledPattern UnhandledPattern{..} =
  renderTerm (contextGammaNames _context) _userPattern

data JesperSt
  = JesperSt
      { _unhandledPatterns :: [UnhandledPattern]
      , _coveredClauseIds  :: Set.Set Int
      }
makeFieldsNoPrefix ''JesperSt

initJesperSt :: JesperSt
initJesperSt = JesperSt [] Set.empty

type HasJesper sig m =
  ( HasBuild sig m
  , Has (C.State JesperSt) sig m
  , Has (C.Reader [VarReplace]) sig m
  )

registerUnhandledTerm :: Has (C.State JesperSt) sig m => UnhandledPattern -> m ()
registerUnhandledTerm p = C.modify @JesperSt $ unhandledPatterns %~ (p :)

------------------------------------------------------------------------
-- * Simplification
------------------------------------------------------------------------

simpClause :: HasJesper sig m => CaseClause -> m (Maybe CaseClause)
simpClause (CaseClause constraints rhs) = runMaybeT do
  (reps, constraints) <- hoistMaybe $ junifyWith decide replaceBounds constraints
  pure $ CaseClause constraints (replaceBounds (maybeToMonoid reps) rhs)
  where
  decide :: CaseConstraint -> Maybe [BoundReplace]
  decide (CaseConstraint test user) = do
    Bound n <- pure user
    pure [BoundReplace n test]

simpProblem :: HasJesper sig m => CaseProblem -> m CaseProblem
simpProblem CaseProblem{..} = do
  _testPattern <- updateVars _testPattern
  _clauses <- forMaybe _clauses simpClause
  pure CaseProblem{..}

------------------------------------------------------------------------
-- * Casing
------------------------------------------------------------------------

underType' :: forall sig m a. GotContext sig m => Type' Term -> ArgCount -> (GammaNames -> Type' Term -> m a) -> m a
underType' = go []
  where
  go delta ty 0 act = act delta ty
  go delta (Pi param retty) count act = underParam param $ go (param^.name : delta) retty (count-1) act
  go delta _ count act = error "bad type"

underType :: forall sig m a. GotContext sig m => Type' Term -> (GammaNames -> Type' Term -> m a) -> m a
underType = go []
  where
  go delta (Pi param retty) act = underParam param $ go (param^.name : delta) retty act
  go delta ty act               = act delta ty

updateVars :: (ReplaceVar a, HasJesper sig m) => a -> m a
updateVars x = do
  r <- C.ask @[VarReplace]
  pure $ replaceVars r x

jContextAt :: HasJesper sig m => Dej -> m (Param Term)
jContextAt dej = do
  param <- contextAtSured dej <$> currentContext
  updateVars param

tryCaseOn :: forall sig m. HasJesper sig m => CaseProblem -> MaybeT m CaseTree
tryCaseOn prob = do
  (dej, userty, tycname, tyc, dtcnames) <- check
  lift do -- avoid MaybeT from accumulating
    arms <- forMaybe dtcnames \dtcname -> runMaybeT do
      dtc <- lookupDefSuredAs _DefDataCon dtcname
      dtcty <- defsNormWith optsReduceAll (dtc^.dtype)
      underType dtcty \delta testty -> do
        let wkn :: Weaken a => a -> a
            wkn = weakenBy delta
            argnames = reverse delta
        C.local @[VarReplace] wkn do
          dej <- pure $ wkn dej
          userty <- pure $ wkn userty
          prob <- pure $ wkn prob
          -- C.sendIO $ putDocLn $ "casing on:" <+> pretty delta <+> pretty dtcname
          testType testty userty do
            let newdejtm = foldSpine (Con DtCon dtcname) (constArgs (levelOf delta))
            C.local @[VarReplace] (VarReplace dej newdejtm :) do
              prob <- updateVars prob
              -- varreps <- C.ask @[VarReplace]
              -- gamma <- contextGammaNames <$> currentContext
              -- C.sendIO $ putDocLn $ list (fmap (renderVarReplace gamma) varreps)
              lift $ CaseDtCon dtcname argnames <$> fromProblem prob
    pure $ CaseOn dej (fromCaseArmList arms)
  where
  testType testty userty action = do
    gamma <- contextGammaNames <$> currentContext
    -- C.sendIO $ putDocLn $ renderTerm gamma testty <+> asymbol "~" <+> renderTerm gamma userty
    (varreps, constraints) <- hoistMaybe $ junifyWith decide replaceVars [CaseConstraint testty userty]
    varreps <- pure $ maybeToMonoid varreps
    C.local @[VarReplace] (varreps <>) action
    where
    decide :: CaseConstraint -> Maybe [VarReplace]
    decide (CaseConstraint test user) = do
      Var dej <- pure user
      pure [VarReplace dej test]

  check = do
    -- check that there is at least one clause, and then get the first one
    firstclause : _ <- pure $ prob^.clauses
    -- find the first constraint with the form '<dej> ~ DtCon <xs> : TyCon <ys>'
    flip asumMap (firstclause^.constraints) \(CaseConstraint ctest cuser) -> do
      Var dej <- pure ctest
      (Con DtCon _, _) <- pure $ unfoldSpine cuser
      param <- jContextAt dej
      (Con TyCon tycname, _) <- pure $ unfoldSpine (param^.argType)
      tyc <- lookupDefSuredAs _DefTypeCon tycname
      Inhabit_DataCons dtcnames <- pure $ tyc^.info.inhabit -- *should* be inhabited by datacons (so avoid case splitting on [external])
      pure (dej, param^.argType, tycname, tyc, dtcnames)

tryFinish :: HasJesper sig m => CaseProblem -> MaybeT m CaseTree
tryFinish prob = do
  clause <- check
  pure $ CaseScope (clause^.rhs)
  where
  check = do
    first : _ <- pure $ prob^.clauses
    pure first

onUnhandled :: HasJesper sig m => CaseProblem -> m CaseTree
onUnhandled prob = do
  ctx <- currentContext
  registerUnhandledTerm (UnhandledPattern ctx (prob^.testPattern))
  pure CaseUnhandled

fromProblem :: HasJesper sig m => CaseProblem -> m CaseTree
fromProblem oldprob = do
  prob <- simpProblem oldprob
  -- ctx <- currentContext
  -- C.sendIO $ putDocLn $ "current env:" <+> renderContext ctx
  -- C.sendIO $ putDocLn $ "original problem:" <+> renderCaseProblem (contextGammaNames ctx) oldprob
  -- C.sendIO $ putDocLn $ "simplified problem:" <+> renderCaseProblem (contextGammaNames ctx) prob
  tryAllOrElse (onUnhandled prob)
    [ tryCaseOn prob
    , tryFinish prob
    ]

checkJesper ::
  forall sig m.
  HasError sig m
  => Range -- ^ where to blame when there is inexhaustive patterm matching
  -> JesperSt -> m ()
checkJesper blameinexhaustive JesperSt{..} = do
  checkUnhandledPatterns
  checkUnusedClauses
  where
  checkUnhandledPatterns :: m ()
  checkUnhandledPatterns = do
    unless (null _unhandledPatterns) do
      C.throwError $ GenericReport $ Err Nothing "Unhandled patterns"
        ( (toPos blameinexhaustive, This "inexhaustive pattern matching, not all cases are considered!")
        : fmap (\pat -> (toPos blameinexhaustive, Where $ "consider: " <> show (renderUnhandledPattern pat))) _unhandledPatterns
        )
        []

  checkUnusedClauses :: m ()
  checkUnusedClauses = do
    -- TODO: implement
    pass


buildPatternFunc ::
  forall sig m.
  ( HasError sig m
  , WithDefs sig m
  , GotContext sig m
  , Has (C.Lift IO) sig m
  )
  => QName
  -> Type' Term
  -> NonEmpty UserClause
  -> m PatternFunc
buildPatternFunc fnname fnty clauses = do
  argcount <- checkArgCounts
  -- forM_ clauses \clause -> do
  --   C.sendIO $ putDocLn $ renderUserClause [] clause
  let caseclauses = fmap (makeCaseClause argcount) clauses

  fnty <- defsNormWith optsReduceAll fnty
  underType' fnty argcount \delta _ -> do
    let argnames = reverse delta
    gamma <- contextGammaNames <$> currentContext
    (jesper, tree) <- C.runState initJesperSt $ C.runReader @[VarReplace] [] $ fromProblem CaseProblem
      { _testPattern = foldSpine (Func fnname) (constArgs argcount)
      , _clauses = toList caseclauses
      }
    checkJesper (head clauses^.range) jesper
    let pm = PatternFunc argnames tree
    -- C.sendIO $ putDocLn $ renderPatternFunc fnname pm
    pure pm
  where
  makeCaseClause :: ArgCount -> UserClause -> CaseClause
  makeCaseClause count (UserClause range patctx lhs rhs) = do
    let subenv = fmap (\param -> Bound (param^.name)) patctx
    let (_, args) = unfoldSpine (subst subenv lhs)
    let rhs' = subst subenv rhs
    let cs = [CaseConstraint test user | (test, user) <- zip (constArgs count) args]
    CaseClause cs rhs'

  userClauseArgCount :: UserClause -> ArgCount
  userClauseArgCount clause = length $ snd $ unfoldSpine (clause^.lhs)

  checkArgCounts :: m ArgCount
  checkArgCounts = do
    let first :| rest = clauses
    let count = userClauseArgCount first
    forM_ rest \this -> do
      let this_count = userClauseArgCount this
      unless (this_count == count) do
        C.throwError $ GenericReport $ Err Nothing "Mismatched argument count"
          [ (toPos (this^.range), This $ "this clause has " <> show this_count <> " argument(s), but expecting " <> show count <> " argument(s)")
          , (toPos (first^.range), Where $ "argument count is determined by this clause")
          ]
          []
    pure count


buildCaseTree ::
  forall sig m.
  ( HasError sig m
  , WithDefs sig m
  , GotContext sig m
  , Has (C.Lift IO) sig m
  )
  => Range
  -> [UserClause]
  -> m CaseTree
buildCaseTree range clauses = do
  let caseclauses = fmap makeCaseClause clauses
  (jesper, tree) <- C.runState initJesperSt $ C.runReader @[VarReplace] [] $ fromProblem CaseProblem
    { _testPattern = Var 0
    , _clauses = caseclauses
    }
  checkJesper range jesper
  pure tree
  where
  makeCaseClause :: UserClause -> CaseClause
  makeCaseClause (UserClause _ patctx lhs rhs) = do
    let subenv = fmap (\param -> Bound (param^.name)) patctx
    let lhs' = subst subenv lhs
    let rhs' = subst subenv rhs
    let cs = [CaseConstraint (Var 0) lhs'] -- `<scrutinee> ~ <lhs>`
    CaseClause cs rhs'
