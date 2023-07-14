module Utils.Set where

import Data.Set

import Relude

intersects :: Ord a => Set a -> Set a -> Bool
intersects a b = not $ disjoint a b
