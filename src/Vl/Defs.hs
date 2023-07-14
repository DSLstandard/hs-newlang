module Vl.Defs where

import Control.Algebra
import Control.Effect.Reader qualified as C
import Control.Effect.State qualified as C

import Data.Default
import Data.HashMap.Strict qualified as HashMap
import Data.Set qualified as Set

import Relude
import Relude.Unsafe qualified as Unsafe

import Vl.Common
import Vl.Lens
import Vl.Name
import Vl.TT
import Vl.Value

-- | Type constructor children
data Inhabit
  = Inhabit_DataCons
      { _dataConNames :: [QName]
      }
  | Inhabit_External

data TypeCon
  = TypeCon
      { _inhabit :: Inhabit
      }
makeFieldsNoPrefix ''TypeCon

data SearchHints
  = SearchHints
      { _instances :: [QName]
      }
makeFieldsNoPrefix ''SearchHints

data Search
  = Search
      { _hints :: SearchHints
      }
makeFieldsNoPrefix ''Search

type UnsolvedNames = Set.Set Name

data Blocked
  = Blocked
      { _term        :: Closed Term
      , _constraints :: NonEmpty UnifyConstraint
      }
makeFieldsNoPrefix ''Blocked

data Def
  = DefClaim
  | DefHole
  | DefBlocked Blocked
  | DefPM PatternFunc
  | DefDataCon
  | DefTypeCon TypeCon
  | DefSearch Search
  | DefUserHole
makePrisms ''Def

referDef :: Def -> QName -> Term
referDef DefDataCon{} = Con DtCon
referDef DefTypeCon{} = Con TyCon
referDef _            = Func

data DefInfo a
  = DefInfo
      { _opInfo :: OpInfo
      , _dtype  :: Closed (Type' Term)
      , _info   :: a
      }
  deriving (Foldable, Functor, Traversable)
makeFieldsNoPrefix ''DefInfo

data Defs
  = Defs
      { _defs        :: HashMap.HashMap QName (DefInfo Def)
      , _searchHints :: SearchHints
      , _guessNames  :: Set.Set QName
      }
makeFieldsNoPrefix ''Defs

emptyDefs :: Defs
emptyDefs = Defs
  { _defs = mempty
  , _searchHints = SearchHints []
  , _guessNames = mempty
  }

defsLookup :: QName -> Defs -> Maybe (DefInfo Def)
defsLookup n ds = ds ^. defs . at n

defsLookupSured :: QName -> Defs -> DefInfo Def
defsLookupSured n ds = case defsLookup n ds of
  Nothing -> error $ "unknown definition: " <> show n
  Just r  -> r

defsSet :: QName -> DefInfo Def -> Defs -> Defs
defsSet n d = defs %~ HashMap.insert n d

defsIsMetaSolved :: QName -> Defs -> Bool
defsIsMetaSolved name = has (defs . ix name . info . _DefPM)

defsToLookup :: Defs -> QName -> Maybe PatternFunc
defsToLookup ds n = ds ^? defs . ix n . traverse . _DefPM

type WithDefs sig m = Has (C.State Defs) sig m

currentDefs :: WithDefs sig m => m Defs
currentDefs = C.get

withDefsRunEval :: WithDefs sig m => EvalOpts -> Eval a -> m a
withDefsRunEval opts tm = do
  lookup <- C.gets defsToLookup
  pure $ runEval (EvalEnv (fmap EvalFuncPM . lookup) opts) tm

defsEval :: WithDefs sig m => Term -> m NF
defsEval = withDefsRunEval optsReduceAll . evaluate

defsNormWith :: WithDefs sig m => EvalOpts -> Term -> m Term
defsNormWith opts = withDefsRunEval opts . normalize

setDef :: WithDefs sig m => QName -> Closed (Type' Term) -> Def -> m ()
setDef n t d = C.modify $ defsSet n DefInfo
  { _opInfo = def
  , _dtype = t
  , _info = d
  }

setDefInfo :: WithDefs sig m => QName -> DefInfo Def -> m ()
setDefInfo name definfo = C.modify $ defsSet name definfo

lookupDef :: WithDefs sig m => QName -> m (Maybe (DefInfo Def))
lookupDef n = C.gets @Defs $ view $ defs . at n

lookupDefSured :: WithDefs sig m => QName -> m (DefInfo Def)
lookupDefSured n = lookupDef n >>= \case
  Nothing -> error $ "unknown definition: " <> show n
  Just r  -> pure r

lookupDefSuredAs :: WithDefs sig m => Prism' Def a -> QName -> m (DefInfo a)
lookupDefSuredAs l n = do
  fmap (^?! l) <$> lookupDefSured n

lookupOpInfoSured :: WithDefs sig m => QName -> m OpInfo
lookupOpInfoSured name = do
  definfo <- lookupDefSured name
  pure $ definfo^.opInfo

searchAmbigNameDef :: WithDefs sig m => AmbigName -> m [(QName, DefInfo Def)]
searchAmbigNameDef n = do
  ds <- C.gets @Defs $ view defs
  pure $ HashMap.toList $ HashMap.filterWithKey (\k v -> n `ambigNameLike` k) ds

updateDef :: WithDefs sig m => QName -> (DefInfo Def -> DefInfo Def) -> m ()
updateDef n f = do
  d <- lookupDefSured n -- fail-safe check
  C.modify $ defsSet n (f d)

isMetaSolved :: WithDefs sig m => QName -> m Bool
isMetaSolved = C.gets @Defs . defsIsMetaSolved

updateHoleToSolution :: WithDefs sig m => QName -> Closed Term -> m ()
updateHoleToSolution n sol = updateDef n $ info .~ DefPM (fromSolution sol)

registerGuessName :: WithDefs sig m => QName -> m ()
registerGuessName n = C.modify @Defs $ guessNames %~ Set.insert n

deregisterGuessName :: WithDefs sig m => QName -> m ()
deregisterGuessName n = C.modify @Defs $ guessNames %~ Set.delete n

------------------------------------------------------------------------
-- * Namespacing
------------------------------------------------------------------------

data Namespacing
  = Namespacing
      { _currentPath :: [Name]
      }
makeFieldsNoPrefix ''Namespacing

initEmptyNamespacing :: Namespacing
initEmptyNamespacing = Namespacing []

initFileNamspacing :: Namespacing
initFileNamspacing = initEmptyNamespacing

type GotNamespacing sig m =
  ( Has (C.Reader Namespacing) sig m
  )

underNamespace :: GotNamespacing sig m => Name -> m a -> m a
underNamespace n = C.local @Namespacing (currentPath %~ (`snoc` n))

makeQNameSingleton :: GotNamespacing sig m => Name -> m QName
makeQNameSingleton name = do
  path <- C.asks @Namespacing $ view currentPath
  pure $ QName path name
