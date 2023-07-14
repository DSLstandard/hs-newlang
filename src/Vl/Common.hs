module Vl.Common where

import Control.Algebra
import Control.Effect.Fresh qualified as C

import Data.Char (isAlphaNum)
import Data.Char qualified as Char
import Data.Default
import Data.Set qualified as Set

import Relude

import Text.Show qualified

import Vl.Lens hiding (universe)

type Type' a = a
type Closed a = a
type UUID = Int
type ArgCount = Int

type GenUUID sig m = Has C.Fresh sig m

freshUUID :: GenUUID sig m => m Int
freshUUID = C.fresh

data AllowTypeHole
  = AllowTypeHole
  | DisallowTypeHole
  deriving (Eq, Show)

data Plicity
  = TheExplicit
  | TheImplicit
  deriving (Eq, Show)

data ImplicitInfo
  = IsImplicit
  | IsInstance
  deriving (Eq, Show)

data PiInfo
  = Explicit
  | Implicit ImplicitInfo
  deriving (Eq, Show)

piInfoIsImplicit :: PiInfo -> Bool
piInfoIsImplicit (Implicit _) = True
piInfoIsImplicit _            = False

data ConInfo
  = TyCon
  | DtCon
  deriving (Eq, Show)

allowedOperatorChars :: Set.Set Char
allowedOperatorChars = Set.fromList "!#$%&*+./<=>?@\\^|-~:"

reservedSymbols :: Set.Set Text
reservedSymbols = Set.fromList
  [ "(", ")" -- parens
  , "{", "}" -- braces
  , "[", "]" -- brackets
  , "," -- comma
  , ":" -- colon
  , "=" -- equals
  , "->", "=>" -- arrows
  , "\\" -- lambda
  , "<-", "|" -- do-notation related
  , "_" -- hole/erased
  , "\"", "'" -- string/char literals, TODO: this may be a bad design
  ]

-- PrimitiveType has ties with reservedKeywords, thus placed in this module
data PrimitiveType
  = PCharType
  | PStringType
  | PIntType
  deriving (Bounded, Enum, Eq, Show)

primitiveTypeWord :: PrimitiveType -> Text
primitiveTypeWord PCharType   = "Char"
primitiveTypeWord PStringType = "String"
primitiveTypeWord PIntType    = "Int"

reservedKeywords :: Set.Set Text
reservedKeywords = Set.fromList $
  [ "where" -- where keyword
  , "[external]" -- [external keyword]
  , "data" -- GADT
  , "struct", "interface", "constructor" -- structbase like stuff
  , "do" -- notation
  , "infixl", "infixr", "infix" -- fixity
  , "instance" -- instance
  , "case", "of" -- case syntax
  , "let", "in" -- let syntax
  , "namespace" -- namespacing
  , "Type" -- Type primitive
  ]
  <> fmap primitiveTypeWord (universe @PrimitiveType)

data Fixity
  = Infixl
  | Infixr
  | Infix
instance Show Fixity where
  show Infixl = "infixl"
  show Infixr = "infixr"
  show Infix  = "infix"

type Precedence = Int

data OpInfo
  = OpInfo
      { _fixity     :: Fixity
      , _precedence :: Precedence
      }
makeFieldsNoPrefix ''OpInfo

instance Show OpInfo where
  show (OpInfo fixity precedence) = show fixity <> " " <> show precedence

instance Default OpInfo where
  def = OpInfo Infix 999
