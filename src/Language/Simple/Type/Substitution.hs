{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
import Language.Simple.Syntax (Constraint (..), Monotype (..))
import Language.Simple.Type.Constraint (GeneratedConstraint (..), UniVar)
import Language.Simple.Util (fromJustOr)

newtype Subst a = Subst (HashMap a (Monotype UniVar))
  deriving (Show)

type Unifier = Subst UniVar

empty :: Subst a
empty = Subst HashMap.empty

singleton :: Hashable a => a -> Monotype UniVar -> Subst a
singleton k v = Subst $ HashMap.singleton k v

compose ::
  ( Eq a,
    Hashable a,
    Substitutable a (Monotype UniVar)
  ) =>
  Subst a ->
  Subst a ->
  Subst a
compose (Subst m1) (Subst m2) = Subst $ HashMap.union (fmap (substitute (Subst m1)) m2) m1

class Substitutable a b where
  substitute :: Subst a -> b -> b

instance Substitutable UniVar GeneratedConstraint where
  substitute s (Constraint q) = Constraint (substitute s q)
  substitute s (ProductGeneratedConstraint c1 c2) = ProductGeneratedConstraint (substitute s c1) (substitute s c2)
  substitute s@(Subst m) (ExistentialGeneratedConstraint vs p c) = ExistentialGeneratedConstraint vs' (substitute s p) (substitute s c)
    where
      vs' = HashSet.difference vs (HashMap.keysSet m)

instance Substitutable UniVar (Constraint UniVar) where
  substitute _ EmptyConstraint = EmptyConstraint
  substitute s (ProductConstraint q1 q2) = ProductConstraint (substitute s q1) (substitute s q2)
  substitute s (EqualityConstraint t1 t2) = EqualityConstraint (substitute s t1) (substitute s t2)

instance Substitutable UniVar (Monotype UniVar) where
  substitute _ (VarType v) = VarType v
  substitute (Subst s) (UniType u) = HashMap.lookup u s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
