module Vl.Unify where

import Control.Carrier.Reader qualified as C
import Control.Carrier.State.Strict qualified as C
import Control.Effect.Error qualified as C
import Control.Monad.Extra (fromMaybeM)

import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Data.Set qualified as Set

import Prettyprinter
import Prettyprinter.Render.Terminal

import Relude

import Utils
import Utils.Map qualified as Map
import Utils.Set qualified as Set

import Vl.Common
import Vl.Defs
import Vl.Error
import Vl.Lens
import Vl.Name
import Vl.TT
import Vl.Value

------------------------------------------------------------------------
-- * Solution
------------------------------------------------------------------------

type USolution = (QName, Closed Term)
type USolutions = Map.Map QName (Closed Term)

renderUSolution :: USolution -> Doc AnsiStyle
renderUSolution (n, sol) = ameta (pretty n) <+> asymbol ":=" <+> renderTerm [] sol

solutionsExists :: USolutions -> Bool
solutionsExists = not . Map.null

solutionsHasAdvanced :: USolutions -> USolutions -> Bool
solutionsHasAdvanced = Map.hasAdvanced

------------------------------------------------------------------------
-- * UResult
------------------------------------------------------------------------

data UResult
  = UResult
      { _solutions   :: USolutions
      , _constraints :: [UnifyConstraint]
      }
makeFieldsNoPrefix ''UResult

instance Semigroup UResult where
  UResult sols1 cs1 <> UResult sols2 cs2 = UResult (sols1 <> sols2) (cs1 <> cs2)

instance Monoid UResult where
  mempty = UResult mempty mempty

initUResult :: UResult
initUResult = UResult Map.empty []

renderUResult :: UResult -> Doc AnsiStyle
renderUResult UResult {..} =
  vsep
    [ nest 2 $ "Constraints:" <+> list (fmap renderUnifyConstraint _constraints),
      nest 2 $ "Solutions:" <+> list (fmap renderUSolution (Map.toList _solutions))
    ]

------------------------------------------------------------------------
-- * Unify monad
------------------------------------------------------------------------

data UnifyEnv
  = UnifyEnv
      { unifyEnvLookup :: QName -> Maybe PatternFunc
        -- only pattern funcs are allowed
      }

newtype Unify a
  = Unify { unUnify :: ReaderT UnifyEnv (StateT UResult Maybe) a }
  deriving
    ( Alternative
    , Applicative
    , Functor
    , Monad
    , MonadReader UnifyEnv
    , MonadState UResult
    )

failUnify :: Unify a
failUnify = empty

registerSolution :: QName -> Closed Term -> Unify ()
registerSolution name ctm = modifying solutions $ Map.insert name ctm

registerConstraint :: GammaNames -> Level -> NF -> NF -> Unify ()
registerConstraint gamma delta lhsnf rhsnf = do
  let lhs = runIdentity $ levelQuoteNF delta lhsnf
  let rhs = runIdentity $ levelQuoteNF delta rhsnf
  ures <- get
  modifying constraints (UnifyConstraint gamma lhs rhs :)

runEvalInUnify :: Eval a -> Unify a
runEvalInUnify act = do
  lookup <- asks unifyEnvLookup
  solutions <- use solutions
  pure $ runEval EvalEnv
    { evalEnvLookup = \name -> asum
        [ EvalFuncPM <$> lookup name,
          EvalFuncPM . fromSolution <$> Map.lookup name solutions
        ]
    , evalEnvOpts = optsReduceAll
    }
    act


runUnify env = usingStateT initUResult . usingReaderT env . unUnify
execUnify env = executingStateT initUResult . usingReaderT env . unUnify

------------------------------------------------------------------------
-- * Pattern unification
------------------------------------------------------------------------


invert :: [NF] -> Maybe (Level, IntMap Dej)
invert [] = pure (0, IntMap.empty)
invert (x : xs) = do
  (lvl, mapping) <- invert xs
  NApp (NVar i) [] <- pure x
  guard $ IntMap.notMember i mapping
  pure (lvl + 1, IntMap.insert i lvl mapping)


-- | this function can straight up fail or just postpone the unification, thus the return type
rename :: Level -> Level -> QName -> IntMap Dej -> NF -> MaybeT Unify Term
rename delta zeta mn map nf = do
  let intoScope sc = rename (delta+1) (zeta+1) mn (IntMap.insert (varDej delta) (varDej (delta-zeta)) map) (runScope sc (var delta))
      go :: NF -> MaybeT Unify Term
      go = rename delta zeta mn map
      tryInvertDej i = do
        j <- hoistMaybe $ IntMap.lookup i map
        pure $ j + zeta
  case nf of
    NType       -> pure $ TType
    NAlien x    -> pure $ Alien x
    NPrim x     -> pure $ Prim x
    NLam n sc   -> Lam n <$> intoScope sc
    NPi a b     -> Pi <$> traverse go a <*> intoScope b
    NApp h args -> do
      args <- traverse go args
      (`foldSpine` args) <$> case h of
        NVar i -> Var <$> tryInvertDej i
        NMeta n ->
          if n == mn
            then lift failUnify -- occurence check
            else pure (Meta n)
        NCon c n -> pure (Con c n)
        NFunc n  -> pure (Func n)
        NBound n -> pure (Bound n)


unifyMeta ::
  GammaNames ->
  Level ->
  -- | swap the constraint?
  Bool ->
  QName ->
  [NF] ->
  NF ->
  Unify ()
unifyMeta gamma delta swap mn margs rhs =
  fromMaybeM
    ( do
        let lhs = NApp (NMeta mn) margs
        if swap
          then registerConstraint gamma delta rhs lhs
          else registerConstraint gamma delta lhs rhs
    )
    ( runMaybeT do
        (lvl, map) <- hoistMaybe $ invert margs
        sol <- lams lvl <$> rename delta 0 mn map rhs
        lift $ registerSolution mn sol
    )

------------------------------------------------------------------------
-- * Other stuff
------------------------------------------------------------------------


levelUnifySpine :: GammaNames -> Level -> NSpine -> NSpine -> Unify ()
levelUnifySpine gamma delta [] [] = pass
levelUnifySpine gamma delta (x : xs) (y : ys) = do
  levelUnifyNF gamma delta x y
  levelUnifySpine gamma delta xs ys
levelUnifySpine gamma delta _ _ = empty


levelUnifyParam :: GammaNames -> Level -> Param NF -> Param NF -> Unify ()
levelUnifyParam gamma delta (Param p1 _ t1) (Param p2 _ t2) = do
  guard $ p1 == p2
  levelUnifyNF gamma delta t1 t2


levelUnifyNF :: GammaNames -> Level -> NF -> NF -> Unify ()
levelUnifyNF gamma delta lhs rhs = do
  let intoScope n = levelUnifyNF (n : gamma) (delta + 1)
  let x = var delta
  lhs <- runEvalInUnify $ forceWknfWith [] lhs
  rhs <- runEvalInUnify $ forceWknfWith [] rhs
  case (lhs, rhs) of
    (NApp (NCon c1 n1) args1, NApp (NCon c2 n2) args2) ->
      guard (c1 == c2 && n1 == n2) *> levelUnifySpine gamma delta args1 args2
    (NApp (NVar i1) args1   , NApp (NVar i2) args2   ) ->
      guard (i1 == i2) *> levelUnifySpine gamma delta args1 args2
    (NApp (NMeta mn1) margs1, NApp (NMeta mn2) margs2) | mn1 == mn2 ->
      guard (levelConvSpine delta margs1 margs2)
    -- Lam
    (NLam n body1, NLam _ body2) ->
      intoScope n (runScope body1 x) (runScope body2 x)
    (NLam n body , other       ) -> do
      other <- runEvalInUnify $ applyNFArg x other
      intoScope n (runScope body x) other
    (other       , NLam n body ) -> do
      other <- runEvalInUnify $ applyNFArg x other
      intoScope n other (runScope body x)
    -- Pi
    (NPi param1 body1, NPi param2 body2) -> do
      levelUnifyParam gamma delta param1 param2
      intoScope (param1^.name) (runScope body1 x) (runScope body2 x)
    -- Meta
    -- ...matching on LHS first gives a more pleasing ordering of solutions, but breaks checkBindHere for some reason (try vhead)
    -- ...matching on RHS first gives a less pleasing ordering of solutions, but does not break checkBindHere (try vhead)
    (NApp (NMeta mn) margs, other                ) ->
      unifyMeta gamma delta False mn margs other
    (other                , NApp (NMeta mn) margs) ->
      unifyMeta gamma delta True  mn margs other
    -- Fallback to conversion
    _ -> do
      guard (convert lhs rhs)
      -- let
      --   lhsdoc = renderTerm gamma (quote lhs)
      --   rhsdoc = renderTerm gamma (quote rhs)
      -- guard (trace ("converting " <> show lhsdoc <> " ~ " <> show rhsdoc) conv lhs rhs)


tryUnifyConstraint :: UnifyConstraint -> Unify ()
tryUnifyConstraint (UnifyConstraint gamma lhs rhs) = do
  lhsnf <- runEvalInUnify $ evaluate lhs
  rhsnf <- runEvalInUnify $ evaluate rhs
  levelUnifyNF gamma 0 lhsnf rhsnf

------------------------------------------------------------------------
-- * Revising
------------------------------------------------------------------------

reviseCurrentConstraints :: Unify ()
reviseCurrentConstraints = do
  fix \repeat -> do
    oldsols <- use solutions
    cs <- constraints <<.= [] -- pop the constraints out of the current state
    traverse_ tryUnifyConstraint cs -- retry the constraints, some may be solved, or even create new solutions
    newsols <- use solutions
    when (solutionsHasAdvanced oldsols newsols) repeat

reviseUnifyNF :: GammaNames -> UnifyEnv -> NF -> NF -> Maybe UResult
reviseUnifyNF gamma uenv lhs rhs = execUnify uenv do
  levelUnifyNF gamma 0 lhs rhs
  reviseCurrentConstraints

reviseUnifyConstraints :: UnifyEnv -> [UnifyConstraint] -> Maybe UResult
reviseUnifyConstraints uenv cs = execUnify uenv do
  traverse_ tryUnifyConstraint cs
  reviseCurrentConstraints

------------------------------------------------------------------------
-- * Utilities
------------------------------------------------------------------------

handleUResult :: HasError sig m => Maybe a -> m a
handleUResult Nothing  = C.throwError $ Inconsistent "unification failed" callStack
handleUResult (Just r) = pure r

defsUnify :: (HasError sig m, GotContext sig m, WithDefs sig m) => NF -> NF -> m UResult
defsUnify lhs rhs = do
  gamma <- contextGammaNames <$> currentContext
  lookup <- C.gets @Defs defsToLookup
  handleUResult $ reviseUnifyNF gamma (UnifyEnv lookup) lhs rhs

defsReviseUnifyConstraints :: (HasError sig m, WithDefs sig m) => [UnifyConstraint] -> m UResult
defsReviseUnifyConstraints cs = do
  lookup <- C.gets @Defs defsToLookup
  handleUResult $ reviseUnifyConstraints (UnifyEnv lookup) cs

defsSetSolutions :: WithDefs sig m => USolutions -> m ()
defsSetSolutions sols = forM_ (Map.toList sols) (uncurry updateHoleToSolution)
