{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Simple.Type.Substitution
  ( Subst (..),
    compose,
    empty,
    singleton,
    Unifier,
    Substitutable (..),
  )
where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (empty, keysSet, lookup, singleton, union)
import qualified Data.HashSet as HashSet (difference)
import Data.Hashable (Hashable)
import Language.Simple.Syntax (Constraint (..), ExtensionConstraint, ExtensionMonotype, Monotype (..))
import Language.Simple.Type.Constraint (GeneratedConstraint (..), UniVar)
import Language.Simple.Util (fromJustOr)

newtype Subst x a = Subst (HashMap a (Monotype x UniVar))

type Unifier x = Subst x UniVar

empty :: Subst x a
empty = Subst HashMap.empty

singleton :: Hashable a => a -> Monotype x UniVar -> Subst x a
singleton k v = Subst $ HashMap.singleton k v

compose ::
  ( Eq a,
    Hashable a,
    Substitutable x a (Monotype x UniVar)
  ) =>
  Subst x a ->
  Subst x a ->
  Subst x a
compose (Subst m1) (Subst m2) = Subst $ HashMap.union (fmap (substitute (Subst m1)) m2) m1

class Substitutable x a b | a b -> x where
  substitute :: Subst x a -> b -> b

instance Substitutable x UniVar (Constraint x UniVar) => Substitutable x UniVar (GeneratedConstraint x) where
  substitute s (Constraint q) = Constraint (substitute s q)
  substitute s (ProductGeneratedConstraint c1 c2) = ProductGeneratedConstraint (substitute s c1) (substitute s c2)
  substitute s@(Subst m) (ExistentialGeneratedConstraint vs p c) = ExistentialGeneratedConstraint vs' (substitute s p) (substitute s c)
    where
      vs' = HashSet.difference vs (HashMap.keysSet m)

instance
  ( Substitutable x UniVar (ExtensionMonotype x UniVar),
    Substitutable x UniVar (ExtensionConstraint x UniVar)
  ) =>
  Substitutable x UniVar (Constraint x UniVar)
  where
  substitute _ EmptyConstraint = EmptyConstraint
  substitute s (ProductConstraint q1 q2) = ProductConstraint (substitute s q1) (substitute s q2)
  substitute s (EqualityConstraint t1 t2) = EqualityConstraint (substitute s t1) (substitute s t2)
  substitute s (ExtensionConstraint x) = ExtensionConstraint $ substitute s x

instance Substitutable x UniVar (ExtensionMonotype x UniVar) => Substitutable x UniVar (Monotype x UniVar) where
  substitute _ (VarType v) = VarType v
  substitute (Subst s) (UniType u) = HashMap.lookup u s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
  substitute s (ExtensionType x) = ExtensionType $ substitute s x
