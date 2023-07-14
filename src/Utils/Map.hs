module Utils.Map where

import Data.Map qualified as Map

import Relude

hasAdvanced :: Ord k => Map k v -> Map k v -> Bool
hasAdvanced old new = do
  not $ Map.null $ Map.difference new old
