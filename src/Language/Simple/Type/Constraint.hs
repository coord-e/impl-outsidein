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
    AtomicConstraint (..),
    GivenConstraint (..),
    GeneratedCoreType,
    GeneratedCoreTermVarBinder,
    GeneratedCoreExpr,
    GeneratedCoreProposition,
    GeneratedCoreCaseArm,
    GeneratedCoreCoercion,
    GeneratedCoreCoercionVarBinder,
    simple,
    EqualityId (..),
    DictionaryId (..),
    AxiomSchemeId (..),
    ImplicationId (..),
    implic,
    Fuv (..),
  )
where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (difference, empty, singleton, toList, union)
import Data.Hashable (Hashable)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (toList)
import GHC.Generics (Generic)
import Language.Core.Syntax (ImplicationId)
import qualified Language.Core.Syntax as Core
import Language.Simple.Fresh (GenFresh (..))
import Language.Simple.Syntax (Class, Constraint (..), Monotype (..), prettyAtomMonotype)
import Numeric.Natural (Natural)
import Prettyprinter (Pretty (..), hsep, nest, parens, sep, space, tupled, unsafeViaShow, (<+>))

newtype AxiomSchemeId = AxiomSchemeId Natural
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance GenFresh AxiomSchemeId where
  fromFreshNatural = AxiomSchemeId

instance Pretty AxiomSchemeId where
  pretty (AxiomSchemeId n) = "$" <> unsafeViaShow n

newtype UniVar = UniVar Natural
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance GenFresh UniVar where
  fromFreshNatural = UniVar

instance Pretty UniVar where
  pretty (UniVar n) = "'u" <> unsafeViaShow n

newtype EqualityId = EqualityId Natural
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance GenFresh EqualityId where
  fromFreshNatural = EqualityId

instance Pretty EqualityId where
  pretty (EqualityId n) = "%c" <> unsafeViaShow n

newtype DictionaryId = DictionaryId Natural
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance GenFresh DictionaryId where
  fromFreshNatural = DictionaryId

instance Pretty DictionaryId where
  pretty (DictionaryId n) = "%d" <> unsafeViaShow n

type GeneratedCoreType = Core.Type UniVar

type GeneratedCoreTermVarBinder = Core.TermVarBinder UniVar

type GeneratedCoreExpr = Core.Expr UniVar EqualityId DictionaryId

type GeneratedCoreProposition = Core.Proposition UniVar

type GeneratedCoreCaseArm = Core.CaseArm UniVar EqualityId DictionaryId

type GeneratedCoreCoercion = Core.Coercion UniVar EqualityId

type GeneratedCoreCoercionVarBinder = Core.CoercionVarBinder UniVar

data AtomicConstraint
  = EqualityAtomicConstraint EqualityId (Monotype UniVar) (Monotype UniVar)
  | TypeClassAtomicConstraint DictionaryId Class (Vector (Monotype UniVar))
  deriving (Generic)

instance Pretty AtomicConstraint where
  pretty (EqualityAtomicConstraint id t1 t2) = pretty id <> ":" <+> pretty t1 <+> "~" <+> pretty t2
  pretty (TypeClassAtomicConstraint id k ts) = pretty id <> ":" <+> hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))

data GivenConstraint
  = EqualityGivenConstraint GeneratedCoreCoercion (Monotype UniVar) (Monotype UniVar)
  | TypeClassGivenConstraint GeneratedCoreExpr Class (Vector (Monotype UniVar))
  deriving (Generic)

instance Pretty GivenConstraint where
  pretty (EqualityGivenConstraint e t1 t2) = Core.prettyAtomCoercion e <> ":" <+> pretty t1 <+> "~" <+> pretty t2
  pretty (TypeClassGivenConstraint e k ts) = Core.prettyAtomExpr e <> ":" <+> hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))

data GeneratedConstraint
  = EmptyGeneratedConstraint
  | AtomicGeneratedConstraint AtomicConstraint
  | ProductGeneratedConstraint GeneratedConstraint GeneratedConstraint
  | ExistentialGeneratedConstraint ImplicationId (HashSet UniVar) [GivenConstraint] GeneratedConstraint
  deriving (Generic)

simple :: GeneratedConstraint -> [AtomicConstraint]
simple EmptyGeneratedConstraint = mempty
simple (AtomicGeneratedConstraint q) = [q]
simple (ProductGeneratedConstraint c1 c2) = simple c1 <> simple c2
simple (ExistentialGeneratedConstraint _ _ _ _) = mempty

implic :: GeneratedConstraint -> [(ImplicationId, HashSet UniVar, [GivenConstraint], GeneratedConstraint)]
implic EmptyGeneratedConstraint = mempty
implic (AtomicGeneratedConstraint _) = mempty
implic (ProductGeneratedConstraint c1 c2) = implic c1 <> implic c2
implic (ExistentialGeneratedConstraint id vs p c) = [(id, vs, p, c)]

instance Semigroup GeneratedConstraint where
  (<>) = ProductGeneratedConstraint

instance Monoid GeneratedConstraint where
  mempty = EmptyGeneratedConstraint

instance Pretty GeneratedConstraint where
  pretty EmptyGeneratedConstraint = "ε"
  pretty (AtomicGeneratedConstraint q) = pretty q
  pretty (ProductGeneratedConstraint c1 c2) = sep [pretty c1, "∧" <+> pretty c2]
  pretty (ExistentialGeneratedConstraint id vs q c) = parens (pretty id) <+> quant <+> parens (nest 2 (qual q <> pretty c))
    where
      quant = "∃" <> hsep (map pretty (HashSet.toList vs)) <> "."
      qual [] = mempty
      qual [q'] = pretty q' <+> "⊃" <> space
      qual qs = tupled (map pretty qs) <+> "⊃" <> space

class Fuv a where
  fuv :: a -> HashSet UniVar

instance Fuv a => Fuv [a] where
  fuv = foldMap fuv

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

instance Fuv AtomicConstraint where
  fuv (EqualityAtomicConstraint _ t1 t2) = HashSet.union (fuv t1) (fuv t2)
  fuv (TypeClassAtomicConstraint _ _ ts) = foldMap fuv ts

instance Fuv GivenConstraint where
  fuv (EqualityGivenConstraint _ t1 t2) = HashSet.union (fuv t1) (fuv t2)
  fuv (TypeClassGivenConstraint _ _ ts) = foldMap fuv ts

instance Fuv GeneratedConstraint where
  fuv EmptyGeneratedConstraint = HashSet.empty
  fuv (AtomicGeneratedConstraint q) = fuv q
  fuv (ProductGeneratedConstraint c1 c2) = HashSet.union (fuv c1) (fuv c2)
  fuv (ExistentialGeneratedConstraint _ vars q c) = HashSet.difference (HashSet.union (fuv q) (fuv c)) vars
