module Vl.SourceStore where

import Control.Algebra
import Control.Effect.State qualified as C

import Data.HashMap.Strict qualified as HashMap

import Error.Diagnose

import Prettyprinter

import Relude

import Vl.Expr
import Vl.Lens

data SourceStore
  = SourceStore
      { _sources :: HashMap.HashMap Origin Text
      }
makeFieldsNoPrefix ''SourceStore

emptySourceStore :: SourceStore
emptySourceStore = SourceStore HashMap.empty

type WithSourceStore sig m =
  ( Has (C.State SourceStore) sig m
  )

sourceStoreRegister :: Origin -> Text -> SourceStore -> SourceStore
sourceStoreRegister origin x = sources %~ HashMap.insert origin x

sourceStoreAddFilesToDiagnostic :: Diagnostic msg -> SourceStore -> Diagnostic msg
sourceStoreAddFilesToDiagnostic diag store =
  foldl' add diag (HashMap.toList (store^.sources))
  where
  add diag (origin, src) = addFile diag (toPath origin) (toString src)

registerSource :: WithSourceStore sig m => Origin -> Text -> m ()
registerSource origin x = C.modify @SourceStore $ sourceStoreRegister origin x

addFilesToDiagnostic :: WithSourceStore sig m => Diagnostic msg -> m (Diagnostic msg)
addFilesToDiagnostic diag = C.gets $ sourceStoreAddFilesToDiagnostic diag
