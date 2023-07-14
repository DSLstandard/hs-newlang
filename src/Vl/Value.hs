module Vl.Value where

import Control.Monad.Extra (fromMaybeM)

import Data.HashMap.Strict qualified as HashMap

import Relude

import Utils

import Vl.Common
import Vl.Lens
import Vl.Name
import Vl.TT

data NHead
  = NVar Dej
  | NBound Name
  | NCon ConInfo QName
  | NFunc QName
  | NMeta QName
  deriving (Show)

type NScope' m z = NF' m z -> m (NF' m z)
type NScope = NScope' Identity Void

runScope :: NScope -> NF -> NF
runScope sc = runIdentity . sc

type NSpine' m z = [NF' m z]
type NSpine = NSpine' Identity Void

type LocalEnv' m z = [NF' m z]

data NF' m z
  = NType
  | NPrim Primitive
  | NApp NHead (NSpine' m z)
  | NLam Name (NScope' m z)
  | NPi (Param (NF' m z)) (NScope' m z)
  | NAlien z

type NF = NF' Identity Void

badSpine :: HasCallStack => a
badSpine = error "logic error: bad spine"

data EvalOpts
  = EvalOpts
      { _reduceFunc :: Bool
      , _reduceMeta :: Bool
      }
makeFieldsNoPrefix ''EvalOpts

optsReduceAll :: EvalOpts
optsReduceAll = EvalOpts
  { _reduceFunc = True
  , _reduceMeta = True
  }

optsReduceMetas :: EvalOpts
optsReduceMetas = EvalOpts
  { _reduceFunc = False
  , _reduceMeta = True
  }

type ForeignFunc m z = [NF' m z] -> Maybe (m (NF' m z))
data EvalFunc m z
  = EvalFuncPM PatternFunc
  | EvalFuncForeign (ForeignFunc m z)

data EvalEnv' m z
  = EvalEnv
      { evalEnvLookup :: QName -> Maybe (EvalFunc m z)
      , evalEnvOpts   :: EvalOpts
      }
type EvalEnv = EvalEnv' Identity Void

newtype EvalT z m a
  = EvalT { unEvalT :: ReaderT (EvalEnv' m z) m a }
  deriving (Applicative, Functor, Monad, MonadReader (EvalEnv' m z))

instance MonadTrans (EvalT z) where
  lift = EvalT . lift

type Eval = EvalT Void Identity

runEvalT :: EvalEnv' m z -> EvalT z m a -> m a
runEvalT evalenv = usingReaderT evalenv . unEvalT

runEval :: EvalEnv -> Eval a -> a
runEval evalenv = usingReader evalenv . unEvalT

----- ============================================================ -----
-- ** Working on Term
----- ============================================================ -----


consumeSpine :: LocalEnv' m z -> NSpine' m z -> Int -> Maybe (LocalEnv' m z, NSpine' m z)
consumeSpine lenv spine 0       = pure (lenv, spine)
consumeSpine lenv [] i          = empty
consumeSpine lenv (x : spine) i = consumeSpine (x : lenv) spine (i - 1)


evalTreeWith :: Monad m => LocalEnv' m z -> NSpine' m z -> CaseTree' z -> MaybeT (EvalT z m) (NF' m z)
evalTreeWith lenv spine CaseUnhandled = empty
evalTreeWith lenv spine (CaseScope term) = lift $ evalTermWith lenv spine term
evalTreeWith lenv spine (CaseOn dej arms) = do
  NApp (NCon DtCon conname) conargs <- lift $ evalVarWith lenv [] dej
  CaseDtCon conname conargns subtree <- hoistMaybe $ HashMap.lookup conname arms
  case consumeSpine lenv conargs (length conargns) of
    Just (lenv, []) -> evalTreeWith lenv spine (generalizeAlien subtree)
    _               -> error "logic error: bad constructor application"


evalAppWith :: forall m z. Monad m => NSpine' m z -> NHead -> EvalT z m (NF' m z)
evalAppWith spine head = withDefault (NApp head spine) do
  opts <- asks evalEnvOpts
  case head of
    NFunc n -> guard (opts^.reduceFunc) *> go NFunc n
    NMeta n -> guard (opts^.reduceMeta) *> go NMeta n
    _       -> empty -- for completeness
  where
    go :: (QName -> NHead) -> QName -> MaybeT (EvalT z m) (NF' m z)
    go h n = MaybeT (asks (`evalEnvLookup` n)) >>= \case
      EvalFuncPM (PatternFunc argns tree) -> do
        (lenv, spine) <- hoistMaybe $ consumeSpine [] spine (length argns)
        evalTreeWith lenv spine (generalizeAlien tree)
      EvalFuncForeign func -> do
        case func spine of
          Nothing -> empty
          Just r  -> lift $ lift r


evalTermWith' lenv = evalTermWith lenv []
evalParamWith lenv = traverse (evalTermWith' lenv)
evalScopeWith lenv scope = do
  evalenv <- ask
  pure (\input -> runEvalT evalenv $ evalTermWith' (input : lenv) scope)

evalVarWith :: Monad m => LocalEnv' m z -> NSpine' m z -> Dej -> EvalT z m (NF' m z)
evalVarWith [] spine dej         = pure $ NApp (NVar dej) spine
evalVarWith (x : lenv) spine 0   = forceWknfWith spine x
evalVarWith (x : lenv) spine dej = evalVarWith lenv spine (dej-1)


evalTermWith :: Monad m => LocalEnv' m z -> NSpine' m z -> Term' z -> EvalT z m (NF' m z)
-- Alien
evalTermWith lenv (_ : _) (Alien x) = badSpine
evalTermWith lenv [] (Alien x) = pure $ NAlien x
-- Prim
evalTermWith lenv (_ : _) (Prim x) = badSpine
evalTermWith lenv [] (Prim x) = pure $ NPrim x
-- TType
evalTermWith lenv (_ : _) TType = badSpine
evalTermWith lenv [] TType = pure $ NType
-- App
evalTermWith lenv spine (App fn arg) = do
  arg <- evalTermWith' lenv arg
  evalTermWith lenv (arg : spine) fn
-- Lam
evalTermWith lenv [] (Lam n scope) =
  NLam n <$> evalScopeWith lenv scope
evalTermWith lenv (arg : spine) (Lam n scope) =
  evalTermWith (arg : lenv) spine scope
-- Pi
evalTermWith lenv (_ : _) (Pi param scope) = badSpine
evalTermWith lenv [] (Pi param scope) =
  NPi <$> evalParamWith lenv param <*> evalScopeWith lenv scope
-- NHead
evalTermWith lenv spine (Con c n) = pure $ NApp (NCon c n) spine
evalTermWith lenv spine (Bound n) = pure $ NApp (NBound n) spine
evalTermWith lenv spine (Func n) = evalAppWith spine (NFunc n)
evalTermWith lenv spine (Meta n) = evalAppWith spine (NMeta n)
evalTermWith lenv spine (Var dej) = evalVarWith lenv spine dej

----- ============================================================ -----
-- ** Working on NF
----- ============================================================ -----

applyNFArg :: Monad m => NF' m z -> NF' m z -> EvalT z m (NF' m z)
applyNFArg arg = forceWknfWith [arg]


forceWknfWith :: Monad m => NSpine' m z -> NF' m z -> EvalT z m (NF' m z)
-- Alien
forceWknfWith [] (NAlien x)                   = pure $ NAlien x
forceWknfWith (_ : _) (NAlien x)              = badSpine
-- Type
forceWknfWith [] NType                        = pure NType
forceWknfWith (_ : _) NType                   = badSpine
-- Prim
forceWknfWith [] (NPrim x)                    = pure $ NPrim x
forceWknfWith (_ : _) (NPrim x)               = badSpine
-- App
forceWknfWith newspine (NApp head spine)      = evalAppWith (spine <> newspine) head
-- Lam
forceWknfWith [] (NLam n scope)               = pure $ NLam n scope
forceWknfWith (arg : newspine) (NLam n scope) = forceWknfWith newspine =<< lift (scope arg)
-- Pi
forceWknfWith [] (NPi param scope)            = pure $ NPi param scope
forceWknfWith (_ : _) (NPi param scope)       = badSpine

------------------------------------------------------------------------
-- * Quoting
------------------------------------------------------------------------

varDej :: Level -> Dej
varDej l = -l-1

var :: Level -> NF' m z
var l = NApp (NVar (varDej l)) [] -- just come up with a neutral term

levelQuoteHead :: Level -> NHead -> Term' z
levelQuoteHead delta nhead =
  case nhead of
    NVar i   -> Var (i + delta)
    NBound n -> Bound n
    NFunc n  -> Func n
    NCon c n -> Con c n
    NMeta n  -> Meta n

levelQuoteNF :: Monad m => Level -> NF' m z -> m (Term' z)
levelQuoteNF delta nf = do
  let quoteScope scope = levelQuoteNF (delta+1) =<< scope (var delta)
  case nf of
    NType ->
      pure $ TType
    NPrim x ->
      pure $ Prim x
    NAlien x ->
      pure $ Alien x
    NApp head spine ->
      foldl' App (levelQuoteHead delta head) <$> traverse (levelQuoteNF delta) spine
    NLam n scope ->
      Lam n <$> quoteScope scope
    NPi param scope ->
      Pi <$> traverse (levelQuoteNF delta) param <*> quoteScope scope

------------------------------------------------------------------------
-- * Conversion
------------------------------------------------------------------------

levelConvHead :: NHead -> NHead -> Bool
levelConvHead (NVar i1)    (NVar i2)    = i1 == i2
levelConvHead (NBound n1)  (NBound n2)  = n1 == n2
levelConvHead (NMeta n1)   (NMeta n2)   = n1 == n2
levelConvHead (NCon c1 n1) (NCon c2 n2) = c1 == c2 && n1 == n2
levelConvHead (NFunc n1)   (NFunc n2)   = n1 == n2
levelConvHead _            _            = False

levelConvSpine :: Level -> NSpine -> NSpine -> Bool
levelConvSpine delta []       []       = True
levelConvSpine delta (x : xs) (y : ys) = levelConvNF delta x y && levelConvSpine delta xs ys
levelConvSpine delta _        _        = False

levelConvParam :: Level -> Param NF -> Param NF -> Bool
levelConvParam delta (Param p1 _ t1) (Param p2 _ t2) =
  p1 == p2 && levelConvNF delta t1 t2

levelConvNF :: Level -> NF -> NF -> Bool
levelConvNF delta lhs rhs = do
  let intoScope = levelConvNF (delta+1)
  let x = var delta
  case (lhs, rhs) of
    (NType, NType) ->
      True
    (NPrim x1, NPrim x2) ->
      convertPrim x1 x2
    (NApp h1 spine1, NApp h2 spine2) ->
      levelConvHead h1 h2 && levelConvSpine delta spine1 spine2
    (NPi param1 scope1, NPi param2 scope2) ->
      levelConvParam delta param1 param2 && intoScope (runScope scope1 x) (runScope scope2 x)
    (NLam _ body1, NLam _ body2) ->
      intoScope (runScope body1 x) (runScope body2 x)
    -- TODO: eta
    -- (NLam n body, other) -> do
    --   other <- applyNFArg x other
    --   intoScope n (body x) other
    -- (other, NLam n body) -> do
    --   other <- applyNFArg x other
    --   intoScope n other (body x)
    _ ->
      False

convertPrim :: Primitive -> Primitive -> Bool
convertPrim = (==)

convert :: NF -> NF -> Bool
convert = levelConvNF 0

------------------------------------------------------------------------
-- * Utilities
------------------------------------------------------------------------

evaluate :: Term -> Eval NF
evaluate = evalTermWith [] []

quotate :: NF' Identity z -> Term' z
quotate = runIdentity . levelQuoteNF 0

normalize :: Term -> Eval Term
normalize = fmap quotate . evaluate
