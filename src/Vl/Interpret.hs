module Vl.Interpret where

import Control.Carrier.State.Strict qualified as C
import Control.Effect.Lift qualified as C

import Data.ByteString qualified as B
import Data.HashMap.Strict qualified as HashMap
import Data.Text.IO qualified as T

import Foreign.Ptr

import Prettyprinter

import Relude

import System.Random

import Utils.Pretty

import Vl.Common
import Vl.Defs
import Vl.Name
import Vl.TT
import Vl.Value

newtype Interpret a
  = Interpret { unInterpret :: ReaderT Defs IO a }
  deriving (Applicative, Functor, Monad, MonadIO)

data VObject
  = VWorld
  | VIORef (IORef (Vl NF'))
  | VHandle Handle
  | VU8 !Word8
  | VU16 !Word16
  | VU32 !Word32
  | VI8 !Int8
  | VI16 !Int16
  | VI32 !Int32
  | VAddr (Ptr ())

instance Pretty VObject where
  pretty VWorld           = "VWorld"
  pretty (VIORef x)       = "[IORef]"
  pretty (VHandle handle) = "Handle " <> show handle
  pretty (VU8  x)         = pretty x
  pretty (VU16 x)         = pretty x
  pretty (VU32 x)         = pretty x
  pretty (VI8  x)         = pretty x
  pretty (VI16 x)         = pretty x
  pretty (VI32 x)         = pretty x
  pretty (VAddr x)        = "pointer"

type Vl f = f IO VObject

class EncodeToNF a where
  encodeToNF :: a -> Vl NF'

mkIO :: Applicative m => Type' (Vl NF') -> IO (Vl NF') -> m (Vl NF')
mkIO a mkresult = pure do
  NApp (NCon DtCon "IO.MkIO")
    [ a
    , NLam "world" \world -> do
        result <- mkresult
        pure $ NApp (NCon DtCon "IORes.MkIORes") [a, world, result]
    ]

mkEntry :: a -> b -> (a, b)
mkEntry fnname make = (fnname, make)

unit :: NF' m z
unit = NApp (NCon TyCon "Unit") []

mkUnit :: NF' m z
mkUnit = NApp (NCon DtCon "Unit.MkUnit") []

fromBool :: Bool -> NF' m z
fromBool True  = NApp (NCon DtCon "Bool.True")  []
fromBool False = NApp (NCon DtCon "Bool.False")  []

lookupForeignFunc :: QName -> Maybe (ForeignFunc IO VObject)
lookupForeignFunc name = HashMap.lookup name $ HashMap.fromList $
  [ mkEntry "str_add" \args -> do
      [NPrim (PString a), NPrim (PString b)] <- pure args
      pure $ pure $ NPrim (PString (a <> b))
  , mkEntry "put_u8" \args -> do
      [NAlien (VHandle handle), NAlien (VU8 b)] <- pure args
      pure $ mkIO unit do
        B.hPut handle (B.singleton b)
        pure mkUnit
  , mkEntry "random_int" \args -> do
      [NPrim (PInt low), NPrim (PInt high)] <- pure args
      pure $ mkIO (NPrim (PType PIntType)) do
        x <- randomRIO (low, high)
        pure $ NPrim (PInt x)
  , mkEntry "int_to_str" \args -> do
      [NPrim (PInt x)] <- pure args
      pure $ pure $ NPrim (PString (show x))
  , mkEntry "putl_str" \args -> do
      [NAlien (VHandle handle), NPrim (PString str)] <- pure args
      pure $ mkIO unit do
        T.hPutStrLn handle str
        pure mkUnit
  , mkEntry "put_str" \args -> do
      [NAlien (VHandle handle), NPrim (PString str)] <- pure args
      pure $ mkIO unit do
        T.hPutStr handle str
        pure mkUnit
  , mkEntry "getl_str" \args -> do
      [NAlien (VHandle handle)] <- pure args
      pure $ mkIO (NPrim (PType PStringType)) do
        str <- T.hGetLine handle
        pure (NPrim (PString str))
  , mkEntry "parse_int" \args -> do
      [NPrim (PString str)] <- pure args
      let a = NApp (NCon TyCon "Maybe") [NPrim (PType PIntType)]
      pure $ pure $ case readMaybe @Integer (toString str) of
        Nothing -> NApp (NCon DtCon "Maybe.None") [a]
        Just x  -> NApp (NCon DtCon "Maybe.Some") [a, NPrim (PInt x)]
  , mkEntry "flush" \args -> do
      [NAlien (VHandle handle)] <- pure args
      pure $ mkIO unit do
        hFlush handle
        pure mkUnit
  ]
  <> iorefOps
  <> intToXOps
  <> handleConsts
  <> intOps
  where
  intOps =
    [ make "int_eq" \x y -> fromBool (x == y)
    , make "int_ne" \x y -> fromBool (x /= y)
    , make "int_gt" \x y -> fromBool (x > y)
    , make "int_ge" \x y -> fromBool (x >= y)
    , make "int_lt" \x y -> fromBool (x < y)
    , make "int_le" \x y -> fromBool (x <= y)
    , make "int_add" \x y -> NPrim (PInt (x + y))
    , make "int_sub" \x y -> NPrim (PInt (x - y))
    , make "int_mul" \x y -> NPrim (PInt (x * y))
    , make "int_div" \x y -> NPrim (PInt (x `div` y))
    , make "int_mod" \x y -> NPrim (PInt (x `mod` y))
    ]
    where
    make fnname f =
      mkEntry fnname \args -> do
        [NPrim (PInt x), NPrim (PInt y)] <- pure args
        pure $ pure $ f x y

  intToXOps =
    [ int_to_x "int_to_u8"  VU8
    , int_to_x "int_to_u16" VU16
    , int_to_x "int_to_u32" VU32
    , int_to_x "int_to_i8"  VI8
    , int_to_x "int_to_i16" VI16
    , int_to_x "int_to_i32" VI32
    ]
    where
    int_to_x name f = mkEntry name \args -> do
      [NPrim (PInt i)] <- pure args
      pure $ do
        pure $ NAlien (f (fromIntegral i))

  handleConsts =
    [ make "stdin"  stdin
    , make "stdout" stdout
    , make "stderr" stderr
    ]
    where
    make fnname handle = mkEntry fnname \args -> do
      [] <- pure args
      pure $ pure $ NAlien (VHandle handle)

  iorefOps =
    [ mkEntry "newIORef" \args -> do
        [ty, tm] <- pure args
        pure $ mkIO (NApp (NCon TyCon "IORef") [ty]) do
          ref <- newIORef tm
          pure $ NAlien (VIORef ref)
    , mkEntry "readIORef" \args -> do
        [ty, NAlien (VIORef ref)] <- pure args
        pure $ mkIO ty do
          readIORef ref
    , mkEntry "writeIORef" \args -> do
        [ty, NAlien (VIORef ref), new] <- pure args
        pure $ mkIO ty do
          writeIORef ref new
          pure mkUnit
    ]

interpret :: Defs -> Term -> IO ()
interpret defs tm = do
  let
    env = EvalEnv
      { evalEnvOpts = optsReduceAll
      , evalEnvLookup = \name -> asum
          [ EvalFuncPM <$> defsToLookup defs name
          , EvalFuncForeign <$> lookupForeignFunc name
          , error $ "unknown function/no definition for: " <> show name
          ]
      }
  -- TODO: pass ty to the function and check that its `IO a`, extract a to replace the hard-coded return type
  let retty = Con TyCon "Unit"
  a <- runEvalT env $ evalTermWith [] [NAlien VWorld]
    $ foldSpine (Func "unIO") [retty, generalizeAlien tm]
  a <- levelQuoteNF 0 a
  C.sendIO $ putDocLn $ "interpret got: " <> renderTerm [] a
  a <- runEvalT env $ evalTermWith [] [] a
  a <- levelQuoteNF 0 a
  C.sendIO $ putDocLn $ "interpret got2: " <> renderTerm [] a
  pass
