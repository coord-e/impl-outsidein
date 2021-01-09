{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Simple.Type.Error
  ( TypeError (..),
  )
where

import GHC.Generics (Generic)
import Language.Simple.Syntax
  ( Constraint (..),
    DataCtor,
    Monotype,
    TermVar,
    TypeVar,
  )
import Language.Simple.Type.Constraint (UniVar)
import Prettyprinter (Pretty (..), dquotes, nest, sep, (<+>))

data TypeError
  = UnboundTermVar TermVar
  | UnboundTypeVar TypeVar
  | UnboundDataCtor DataCtor
  | ConflictingTypeVars TypeVar
  | MismatchedNumberOfDataCtorFields
      { ctor :: DataCtor,
        expected :: Int,
        got :: Int
      }
  | UnresolvedConstraint (Constraint UniVar)
  | MatchingGivenConstraint (Constraint UniVar)
  | OccurCheckError (Monotype UniVar) (Monotype UniVar)
  | MismatchedTypes (Monotype UniVar) (Monotype UniVar)
  deriving (Generic)

instance Pretty TypeError where
  pretty (UnboundTermVar x) = "unbound variable:" <+> pretty x
  pretty (UnboundTypeVar a) = "unbound type variable:" <+> pretty a
  pretty (UnboundDataCtor k) = "unbound data constructor:" <+> pretty k
  pretty (ConflictingTypeVars a) = "conflicting type variable definitions:" <+> pretty a
  pretty MismatchedNumberOfDataCtorFields {ctor, expected, got} =
    nest 2 $
      sep
        [ "mismatched number of fields on data constructor"
            <+> dquotes (pretty ctor),
          "expected"
            <+> pretty expected,
          "but got"
            <+> pretty got
        ]
  pretty (UnresolvedConstraint q) = "unresolved constraint:" <+> pretty q
  pretty (MatchingGivenConstraint q) = "the constraint" <+> pretty q <+> "matches an instance declaration"
  pretty (OccurCheckError t1 t2) = "occur check failed:" <+> pretty t1 <+> "~" <+> pretty t2
  pretty (MismatchedTypes t1 t2) =
    "could not match expected type"
      <+> dquotes (pretty t1)
      <+> "with actual type"
      <+> dquotes (pretty t2)
