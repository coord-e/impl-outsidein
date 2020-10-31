{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Language.Simple.Type.Error
  ( TypeError (..),
  )
where

import GHC.Generics (Generic)
import Language.Simple.Syntax (Constraint (..), DataCtor, Monotype (..), TermVar, TypeVar)
import Language.Simple.Type.Constraint (UniVar)
import Prettyprinter (Doc, Pretty (..), dquotes, nest, sep, squotes, vsep, (<+>))

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
  deriving (Show, Generic)

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
  pretty (UnresolvedConstraint q) = vsep $ prettyUnresolvedConstraint q

prettyUnresolvedConstraint :: Constraint UniVar -> [Doc ann]
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
