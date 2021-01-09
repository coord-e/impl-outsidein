{-# LANGUAGE DeriveGeneric #-}

module Language.Core.Type.Error (TypeError (..)) where

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
  deriving (Generic)
