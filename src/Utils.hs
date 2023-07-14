module Utils where

import Control.Monad.Extra (fromMaybeM)

import Relude

withDefault :: Monad m => a -> MaybeT m a -> m a
withDefault x = fromMaybeM (pure x) . runMaybeT

tryAllOrElse :: (Monad m) => m a -> [MaybeT m a] -> m a
tryAllOrElse fall = fromMaybeM fall . runMaybeT . asum

subscript :: Char -> Char
subscript '0' = '₀'
subscript '1' = '₁'
subscript '2' = '₂'
subscript '3' = '₃'
subscript '4' = '₄'
subscript '5' = '₅'
subscript '6' = '₆'
subscript '7' = '₇'
subscript '8' = '₈'
subscript '9' = '₉'
subscript c   = c

findWithIndex :: (a -> Bool) -> [a] -> Maybe (Int, a)
findWithIndex p = go 0
  where
  go i []       = empty
  go i (x : xs) = if p x then pure (i, x) else go (i+1) xs
