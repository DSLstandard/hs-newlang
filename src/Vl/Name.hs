module Vl.Name where

import Data.List qualified as List
import Data.Text qualified as T

import Prettyprinter

import Relude
import Relude.Unsafe qualified as Unsafe

import Text.Show qualified

import Vl.Common
import Vl.Lens

data Name
  = UserName Text
  | VirtName Text UUID
  deriving (Eq, Generic, Ord)

instance IsString Name where
  fromString = UserName . fromString

instance Hashable Name

instance Show Name where
  show (UserName n)   = toString n
  show (VirtName n i) = toString n <> ":" <> show i

instance Pretty Name where
  pretty = viaShow

boringName :: Name
boringName = VirtName "_" 0

nameRoot :: Name -> Text
nameRoot (UserName n)   = n
nameRoot (VirtName n i) = n

isNameBoring :: Name -> Bool
isNameBoring = (== "_") . nameRoot

data QName
  = QName
      { _path :: [Name]
      , _name :: Name
      }
  deriving (Eq, Generic, Ord)
makeFieldsNoPrefix ''QName

instance Hashable QName

instance Show QName where
  show (QName path name) = namesToString path name

instance Pretty QName where
  pretty = viaShow

splitStringToNames :: String -> ([Name], Name)
splitStringToNames input = do
  let xs = fmap UserName $ T.splitOn "." (T.pack input)
  (Unsafe.init xs, Unsafe.last xs)

namesToString :: [Name] -> Name -> String
namesToString path n = mconcat $ intersperse "." $ fmap show $ path `snoc` n

instance IsString QName where
  fromString input = let (xs, x) = splitStringToNames input in QName xs x

qnameSingleton :: Name -> QName
qnameSingleton = QName []

data AmbigName
  = AmbigName
      { _path :: [Name]
        -- potentionally empty path name
      , _name :: Name
      }
  deriving (Eq)

instance IsString AmbigName where
  fromString input = let (xs, x) = splitStringToNames input in AmbigName xs x

instance Show AmbigName where
  show (AmbigName path name) = namesToString path name

instance Pretty AmbigName where
  pretty = viaShow

ambigNameSingleton :: Name -> AmbigName
ambigNameSingleton = AmbigName []

ambigNameSingle :: AmbigName -> Maybe Name
ambigNameSingle (AmbigName [] name) = pure name
ambigNameSingle _                   = empty

ambigNameLike :: AmbigName -> QName -> Bool
ambigNameLike (AmbigName apath aname) (QName qpath qname) = do
  let a = apath <> [aname]
  let q = qpath <> [qname]
  a `List.isSuffixOf` q

newtype NewMetaName
  = NewMetaName { unNewMetaName :: QName }
  deriving (Pretty, Show)
    via QName
