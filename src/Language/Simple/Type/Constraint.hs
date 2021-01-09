{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Language.Simple.Type.Constraint
  ( UniVar (..),
    GeneratedConstraint (..),
    simple,
    implic,
    reduce,
    isEmpty,
    Fuv (..),
  )
where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (difference, empty, singleton, toList, union)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Language.Simple.Fresh (GenFresh (..))
import Language.Simple.Syntax (Constraint (..), Monotype (..))
import Numeric.Natural (Natural)
import Prettyprinter (Pretty (..), hsep, nest, parens, sep, space, unsafeViaShow, (<+>))

newtype UniVar = UniVar Natural
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance GenFresh UniVar where
  fromFreshNatural = UniVar

instance Pretty UniVar where
  pretty (UniVar n) = "'u" <> unsafeViaShow n

data GeneratedConstraint
  = Constraint (Constraint UniVar)
  | ProductGeneratedConstraint GeneratedConstraint GeneratedConstraint
  | ExistentialGeneratedConstraint (HashSet UniVar) (Constraint UniVar) GeneratedConstraint
  deriving (Generic)

simple :: GeneratedConstraint -> Constraint UniVar
simple (Constraint q) = q
simple (ProductGeneratedConstraint c1 c2) = simple c1 <> simple c2
simple (ExistentialGeneratedConstraint _ _ _) = mempty

implic :: GeneratedConstraint -> [(HashSet UniVar, Constraint UniVar, GeneratedConstraint)]
implic (Constraint _) = mempty
implic (ProductGeneratedConstraint c1 c2) = implic c1 <> implic c2
implic (ExistentialGeneratedConstraint vs p c) = [(vs, p, c)]

reduce :: Constraint a -> Constraint a
reduce (ProductConstraint q1 q2) = reduce1 (ProductConstraint (reduce q1) (reduce q2))
  where
    reduce1 (ProductConstraint EmptyConstraint EmptyConstraint) = EmptyConstraint
    reduce1 (ProductConstraint EmptyConstraint q) = q
    reduce1 (ProductConstraint q EmptyConstraint) = q
    reduce1 q = q
reduce q = q

isEmpty :: Constraint a -> Bool
isEmpty EmptyConstraint = True
isEmpty _ = False

instance Semigroup GeneratedConstraint where
  (<>) = ProductGeneratedConstraint

instance Monoid GeneratedConstraint where
  mempty = Constraint mempty

instance Pretty GeneratedConstraint where
  pretty (Constraint q) = pretty q
  pretty (ProductGeneratedConstraint c1 c2) = sep [pretty c1, "∧" <+> pretty c2]
  pretty (ExistentialGeneratedConstraint vs q c) = quant <+> parens (nest 2 (qual q <> pretty c))
    where
      quant = "∃" <> hsep (map pretty (HashSet.toList vs)) <> "."
      qual EmptyConstraint = mempty
      qual _ = pretty q <+> "⊃" <> space

class Fuv a where
  fuv :: a -> HashSet UniVar

instance Fuv (Monotype UniVar) where
  fuv (VarType _) = HashSet.empty
  fuv (ApplyType _ ts) = foldMap fuv ts
  fuv (UniType u) = HashSet.singleton u
  fuv (FamilyApplyType _ ts) = foldMap fuv ts

instance Fuv (Constraint UniVar) where
  fuv EmptyConstraint = HashSet.empty
  fuv (ProductConstraint q1 q2) = HashSet.union (fuv q1) (fuv q2)
  fuv (EqualityConstraint t1 t2) = HashSet.union (fuv t1) (fuv t2)
  fuv (TypeClassConstraint _ ts) = foldMap fuv ts

instance Fuv GeneratedConstraint where
  fuv (Constraint q) = fuv q
  fuv (ProductGeneratedConstraint c1 c2) = HashSet.union (fuv c1) (fuv c2)
  fuv (ExistentialGeneratedConstraint vars q c) = HashSet.difference (HashSet.union (fuv q) (fuv c)) vars
