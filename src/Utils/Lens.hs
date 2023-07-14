module Utils.Lens where

import Control.Lens
import Control.Lens.Internal.FieldTH

import Data.Char qualified as Char
import Data.List qualified as List

import Language.Haskell.TH

import Relude

makeFieldsFor :: Name -> [String] -> DecsQ
makeFieldsFor name fields = makeFieldOptics
  (defaultFieldRules & lensField .~ namer) name
  where
  namer _ _ field = maybeToList $ do
    fieldUnprefixed <- List.stripPrefix "_" (nameBase field)
    guard $ fieldUnprefixed `elem` fields
    let className  = "Has" ++ overHead Char.toUpper fieldUnprefixed
        methodName = fieldUnprefixed
    return (MethodName (mkName className) (mkName methodName))

  overHead _ []     = []
  overHead f (x:xs) = f x : xs
