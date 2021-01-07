{-# LANGUAGE DeriveGeneric #-}

module Language.Core.Type.Error (TypeError (..)) where

import GHC.Generics (Generic)
import Language.Core.Syntax
  ( AxiomName,
    CoercionVar,
    DataCtor,
    Proposition,
    TermVar,
    Type,
    TypeCtor,
    TypeVar,
  )

data TypeError
  = UnboundDataCtor DataCtor
  | UnboundTermVar TermVar
  | UnboundTypeVar TypeVar
  | UnboundCoercionVar CoercionVar
  | UnboundAxiomName AxiomName
  | FunctionTypeExpected Type
  | ApplyTypeExpected Type
  | ForallTypeExpected Type
  | CoercionForallTypeExpected Type
  | TypeMismatch Type Type
  | TypeCtorMismatch TypeCtor TypeCtor
  | LengthMismatch Int Int
  | PropositionMismatch Proposition Proposition
  | DuplicateTypeVar TypeVar
  | DuplicateCoercionVar CoercionVar
  deriving (Generic)
