module Vl.Error where

import Control.Algebra
import Control.Effect.Error qualified as C

import Data.Text

import Error.Diagnose

import Prettyprinter

import Relude

data Error
  = GenericReport (Report Text)
  | GenericDiagnostic (Diagnostic Text)
  | Inconsistent Text CallStack

errorToDiagnostic :: Error -> Diagnostic Text
errorToDiagnostic (GenericReport report)   = addReport def report
errorToDiagnostic (GenericDiagnostic diag) = diag
errorToDiagnostic (Inconsistent msg cs)    = addReport def $
  Err Nothing "Inconsistency" []
    [ Note $ "Message: " <> msg
    , Note $ "CallStack: " <> show cs
    , Note "This error *logically* should not be presented to the user."
    ]

type HasError sig m =
  ( HasCallStack
  , Has (C.Error Error) sig m
  )

simpleErr :: Pretty msg => msg -> [(Position, Marker msg)] -> [Note msg] -> Report msg
simpleErr = Err Nothing

uponInconsistency :: HasError sig m => m a -> m a -> m a
uponInconsistency handle act = do
  C.catchError act \case
    Inconsistent s cs -> handle
    err               -> C.throwError err
