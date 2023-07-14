{-# LANGUAGE InstanceSigs #-}

module Vl.Expr where

import Error.Diagnose qualified as Diagnostic

import Prettyprinter

import Relude

import Text.Show qualified

import Vl.Common
import Vl.Lens
import Vl.Name
import Vl.TT

newtype Loc
  = Loc { unLoc :: (Int, Int) }

instance Show Loc where
  show (Loc (row, col)) = "(" <> show row <> "," <> show col <> ")"

instance Pretty Loc where
  pretty = viaShow

data Origin
  = FromFile Text
  | FromVirt Text UUID
  deriving (Eq, Generic, Ord)

instance Hashable Origin

toPath :: Origin -> FilePath
toPath (FromFile x)   = toString x
toPath (FromVirt x i) = "<" <> toString x <> ":" <> show i <> ">"

instance Show Origin where
  show = toPath

instance Pretty Origin where
  pretty = viaShow

data Range
  = Range
      { rangeStart  :: Loc
      , rangeEnd    :: Loc
      , rangeOrigin :: Origin
      }

toPos :: Range -> Diagnostic.Position
toPos (Range start end origin) =
  Diagnostic.Position (unLoc start) (unLoc end) (toPath origin)

instance Show Range where
  show Range {..} = show rangeOrigin <> ":" <> show rangeStart <> "-" <> show rangeEnd

instance Pretty Range where
  pretty = viaShow

instance Semigroup Range where
  -- NOTE: the second origin must be dropped
  Range (Loc start1) (Loc end1) origin <> Range (Loc start2) (Loc end2) _ =
    Range (Loc (min start1 start2)) (Loc (max end1 end2)) origin

data AppArg a
  = AppArg
      { _appRange :: Range
      , _arg      :: a
      }
  deriving (Foldable, Functor, Traversable)

makeFieldsNoPrefix ''AppArg

data EArg
  = EArg
      { _range   :: Range
      , _plicity :: Plicity
      , _arg     :: Expr
      }
  deriving (Show)

data EParam
  = EParam
      { _range     :: Range
      , _piInfo    :: PiInfo
      , _name      :: Name
      , _nameRange :: Range
      , _argType   :: Type' Expr
      }
  deriving (Show)

instance ToLevel EParam where
  levelOf _ = 1

instance ToLevel [EParam] where
  levelOf = length

data EClause
  = EClause
      { _range :: Range
      , _lhs   :: Expr
      , _rhs   :: Expr
      }
  deriving (Show)

data ECaseBase
  = ECaseBase
      { _range     :: Range
      , _scrutinee :: Expr
      , _clauses   :: [EClause]
      }
  deriving (Show)

data Expr
  = EPrim
      { _range     :: Range
      , _primitive :: Primitive
      }
  | EType
      { _range :: Range
      }
  | EVar
      { _range   :: Range
      , _varName :: AmbigName
      }
  | EResolvedVar
      { _range         :: Range
      , _qualifiedName :: QName
      }
  | EApp
      { _range :: Range
      , _func  :: Expr
      , _arg   :: EArg
      }
  | EPi
      { _range :: Range
      , _param :: EParam
      , _scope :: Type' Expr
      }
  | ELam
      { _range :: Range
      , _param :: EParam
      , _scope :: Type' Expr
      }
  | EHole
      { _range :: Range
      }
  | EUserHole
      { _range :: Range
      , _name  :: Name
      }
  | EOpTree
      { _leftArg     :: Expr
      , _opName      :: AmbigName
      , _opNameRange :: Range
      , _rightTree   :: Expr
      }
  | ECase ECaseBase
  | ELet ECaseBase
  deriving (Show)

makeFieldsNoPrefix ''EParam
makeFieldsNoPrefix ''ECaseBase
makeFieldsNoPrefix ''EClause
makeFieldsNoPrefix ''EArg
makeFieldsNoPrefix ''AmbigName

exprRange :: Expr -> Range
exprRange EPrim {..} = _range
exprRange EType {..} = _range
exprRange EVar {..} = _range
exprRange EResolvedVar {..} = _range
exprRange EApp {..} = _range
exprRange EPi {..} = _range
exprRange ELam {..} = _range
exprRange EHole {..} = _range
exprRange EUserHole {..} = _range
exprRange (ECase ECaseBase {..}) = _range
exprRange (ELet ECaseBase {..}) = _range
exprRange EOpTree {..} =
  exprRange _leftArg <> _opNameRange <> exprRange _rightTree

exprFoldExplicitSpine :: Range -> Expr -> [Expr] -> Expr
exprFoldExplicitSpine range =
  foldl' (\func arg -> EApp range func (EArg (exprRange arg) TheExplicit arg))

data EClaim
  = EClaim
      { _range     :: Range
      , _name      :: Name
      , _nameRange :: Range
      , _dtype     :: Type' Expr
      }

makeFieldsNoPrefix ''EClaim

data EConstructor
  = EConstructor
      { _range     :: Range
      , _name      :: Name
      , _nameRange :: Range
      , _dtype     :: Type' Expr
      }

makeFieldsNoPrefix ''EConstructor

data EInhabit
  = EInhabit_DataCons
      { _dataCons :: [EConstructor]
      }
  | EInhabit_External

data EData
  = EData
      { _typeConstructor :: EConstructor
      , _inhabit         :: EInhabit
      }

makeFieldsNoPrefix ''EData

data EStructBase
  = EStructBase
      { _tycName      :: Name
      , _tycNameRange :: Range
      , _tycParams    :: [EParam]
      , _dtcName      :: Name
      , _dtcNameRange :: Range
      , _dtcParams    :: [EParam]
      }

makeFieldsNoPrefix ''EStructBase

data EInstance
  = EInstance
      { _range     :: Range
      , _name      :: AmbigName
      , _nameRange :: Range
      }

makeFieldsNoPrefix ''EInstance

data EFixity
  = EFixity
      { _range     :: Range
      , _opInfo    :: OpInfo
      , _name      :: AmbigName
      , _nameRange :: Range
      }

makeFieldsNoPrefix ''EFixity

data ENamespace
  = ENamespace
      { _name :: Name
      , _defs :: [EDef]
      }

data EDef
  = EDefClaim EClaim
  | EDefData EData
  | EDefClause EClause
  | EDefStruct EStructBase
  | EDefInterface EStructBase
  | EDefInstance EInstance
  | EDefFixity EFixity
  | EDefNamespace ENamespace

data EFile
  = EFile
      { _defs :: [EDef]
      }

makeFieldsNoPrefix ''EFile
