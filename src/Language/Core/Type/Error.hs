{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Core.Type.Error (TypeError (..)) where

import Data.Vector (Vector)
import GHC.Generics (Generic)
import Language.Core.Syntax
  ( AxiomName,
    CoercionVar,
    CompleteProposition,
    CompleteType,
    DataCtor,
    TermVar,
    TypeCtor,
    TypeVar,
  )
import Prettyprinter (Pretty (..), viaShow, (<+>))

data TypeError
  = UnboundDataCtor DataCtor
  | UnboundTermVar TermVar
  | UnboundTypeVar TypeVar
  | UnboundCoercionVar CoercionVar
  | UnboundAxiomName AxiomName
  | FunctionTypeExpected CompleteType
  | ApplyTypeExpected CompleteType
  | ForallTypeExpected CompleteType
  | CoercionForallTypeExpected CompleteType
  | TypeMismatch CompleteType CompleteType
  | TypeCtorMismatch TypeCtor TypeCtor
  | LengthMismatch Int Int
  | PropositionMismatch CompleteProposition CompleteProposition
  | DuplicateTypeVar TypeVar
  | DuplicateCoercionVar CoercionVar
  | InvalidIndex (Vector CompleteType) Int
  deriving (Show, Eq, Generic)

instance Pretty TypeError where
  pretty (PropositionMismatch p1 p2) = "proposition mismatch:" <+> pretty p1 <+> "vs" <+> pretty p2
  pretty (TypeMismatch t1 t2) = "type mismatch:" <+> pretty t1 <+> "vs" <+> pretty t2
  pretty x = viaShow x
