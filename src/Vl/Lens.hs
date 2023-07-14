module Vl.Lens
( module Vl.Lens
, module Control.Lens
) where

import Control.Lens hiding (Context, Context', Level)

class HasName a b | a -> b where
  name :: Lens' a b

class HasArgType a b | a -> b where
  argType :: Lens' a b

class HasArg a b | a -> b where
  arg :: Lens' a b

class HasDtype a b | a -> b where
  dtype :: Lens' a b

class HasValue a b | a -> b where
  value :: Lens' a b

class HasConstraints a b | a -> b where
  constraints :: Lens' a b

class HasInhabit a b | a -> b where
  inhabit :: Lens' a b

class HasOpInfo a b | a -> b where
  opInfo :: Lens' a b
