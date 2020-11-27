{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Simple.Type.Error
  ( TypeError (..),
    ExtensionTypeError,
  )
where

import GHC.Generics (Generic)
import Language.Simple.Syntax
  ( Constraint (..),
    DataCtor,
    ExtensionConstraint,
    ExtensionMonotype,
    TermVar,
    TypeVar,
  )
import Language.Simple.Type.Constraint (UniVar)
import Prettyprinter (Pretty (..), dquotes, nest, sep, (<+>))

data family ExtensionTypeError x

data TypeError x
  = UnboundTermVar TermVar
  | UnboundTypeVar TypeVar
  | UnboundDataCtor DataCtor
  | ConflictingTypeVars TypeVar
  | MismatchedNumberOfDataCtorFields
      { ctor :: DataCtor,
        expected :: Int,
        got :: Int
      }
  | UnresolvedConstraint (Constraint x UniVar)
  | ExtensionTypeError (ExtensionTypeError x)
  deriving (Generic)

instance
  ( Pretty (ExtensionMonotype x UniVar),
    Pretty (ExtensionConstraint x UniVar),
    Pretty (ExtensionTypeError x)
  ) =>
  Pretty (TypeError x)
  where
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
  pretty (ExtensionTypeError x) = pretty x
