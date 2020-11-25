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
    Monotype (..),
    TermVar,
    TypeVar,
  )
import Language.Simple.Type.Constraint (UniVar)
import Prettyprinter (Doc, Pretty (..), dquotes, nest, sep, squotes, vsep, (<+>))

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
  pretty (UnresolvedConstraint q) = nest 2 . vsep $ prettyUnresolvedConstraint q
  pretty (ExtensionTypeError x) = pretty x

prettyUnresolvedConstraint ::
  ( Pretty (ExtensionMonotype x UniVar),
    Pretty (ExtensionConstraint x UniVar)
  ) =>
  Constraint x UniVar ->
  [Doc ann]
prettyUnresolvedConstraint EmptyConstraint = []
prettyUnresolvedConstraint (ProductConstraint q1 q2) = prettyUnresolvedConstraint q1 <> prettyUnresolvedConstraint q2
prettyUnresolvedConstraint (EqualityConstraint t1 t2) =
  [ nest 2 $
      vsep
        ( "could not match expected type"
            <+> squotes (pretty t1)
            <+> "with actual type"
            <+> squotes (pretty t2) :
          additionalInfo t1 t2
        )
  ]
  where
    additionalInfo (UniType u) _ = [pretty u <+> "is untouchable"]
    additionalInfo _ (UniType u) = [pretty u <+> "is untouchable"]
    additionalInfo (VarType a) _ = [dquotes (pretty a) <+> "is a rigid type variable"]
    additionalInfo _ (VarType a) = [dquotes (pretty a) <+> "is a rigid type variable"]
    additionalInfo _ _ = []
prettyUnresolvedConstraint (ExtensionConstraint x) = ["unresolved constraint:" <+> pretty x]
