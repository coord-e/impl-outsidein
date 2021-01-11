{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Simple.Type.Substitution
  ( Subst (..),
    limit,
    compose,
    merge,
    domain,
    null,
    lookup,
    empty,
    member,
    singleton,
    replaceAll,
    fromBinders,
    Unifier,
    Instantiator,
    Substitutable (..),
  )
where

import Control.Monad.Except (MonadError (..))
import Data.Foldable (foldlM)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
  ( empty,
    insert,
    intersection,
    keysSet,
    lookup,
    member,
    null,
    singleton,
    toList,
    union,
  )
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (toMap)
import Data.Hashable (Hashable)
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax (Constraint (..), Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (AtomicConstraint (..), GeneratedConstraint (..), GivenConstraint (..), UniVar)
import Language.Simple.Type.Error (TypeError (..))
import Prettyprinter (Pretty (..), list, (<+>))
import Util (fromJustOr, orThrow)
import Prelude hiding (lookup, null)

newtype Subst a = Subst (HashMap a (Monotype UniVar))

type Unifier = Subst UniVar

type Instantiator = Subst TypeVar

instance Pretty a => Pretty (Subst a) where
  pretty (Subst m) = list . map f $ HashMap.toList m
    where
      f (k, v) = pretty k <+> "↦" <+> pretty v

empty :: Subst a
empty = Subst HashMap.empty

null :: Subst a -> Bool
null (Subst m) = HashMap.null m

member :: (Hashable a, Eq a) => a -> Subst a -> Bool
member k (Subst m) = HashMap.member k m

lookup :: (Hashable a, Eq a) => a -> Subst a -> Maybe (Monotype UniVar)
lookup k (Subst m) = HashMap.lookup k m

domain :: Subst a -> HashSet a
domain (Subst m) = HashMap.keysSet m

limit :: (Hashable a, Eq a) => HashSet a -> Subst a -> Subst a
limit s (Subst m) = Subst . HashMap.intersection m $ HashSet.toMap s

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

merge ::
  (Eq a, Hashable a, MonadFail m) =>
  (a -> Monotype UniVar) ->
  (Monotype UniVar -> Monotype UniVar -> Bool) ->
  Subst a ->
  Subst a ->
  m (Subst a)
merge c p (Subst m1) (Subst m2)
  | agree = pure . Subst $ HashMap.union m1 m2
  | otherwise = fail "Subst.merge"
  where
    agree = all check (HashMap.keysSet (m1 `HashMap.intersection` m2))
    check v = p (HashMap.lookup v m1 `fromJustOr` c v) (HashMap.lookup v m2 `fromJustOr` c v)

replaceAll :: MonadError TypeError m => Instantiator -> TypeVar -> m (Monotype UniVar)
replaceAll m v = lookup v m `orThrow` UnboundTypeVar v

fromBinders :: (Eq a, Hashable a, Fresh m, Foldable f) => f a -> m (Subst a)
fromBinders = foldlM go empty
  where
    go (Subst subst) v = do
      a <- fresh
      pure . Subst $ HashMap.insert v (UniType a) subst

class Substitutable a b where
  substitute :: Subst a -> b -> b

instance Substitutable a b => Substitutable a [b] where
  substitute s = map (substitute s)

instance Substitutable UniVar GeneratedConstraint where
  substitute _ EmptyGeneratedConstraint = EmptyGeneratedConstraint
  substitute s (AtomicGeneratedConstraint q) = AtomicGeneratedConstraint (substitute s q)
  substitute s (ProductGeneratedConstraint c1 c2) = ProductGeneratedConstraint (substitute s c1) (substitute s c2)
  substitute s (ExistentialGeneratedConstraint id vs p c) = ExistentialGeneratedConstraint id vs (substitute s p) (substitute s c)

instance Substitutable a (Monotype UniVar) => Substitutable a AtomicConstraint where
  substitute s (EqualityAtomicConstraint id t1 t2) = EqualityAtomicConstraint id (substitute s t1) (substitute s t2)
  substitute s (TypeClassAtomicConstraint id k ts) = TypeClassAtomicConstraint id k $ fmap (substitute s) ts

instance Substitutable a (Monotype UniVar) => Substitutable a GivenConstraint where
  substitute s (EqualityGivenConstraint e t1 t2) = EqualityGivenConstraint e (substitute s t1) (substitute s t2)
  substitute s (TypeClassGivenConstraint e k ts) = TypeClassGivenConstraint e k $ fmap (substitute s) ts

instance Substitutable a (Monotype UniVar) => Substitutable a (Constraint UniVar) where
  substitute _ EmptyConstraint = EmptyConstraint
  substitute s (ProductConstraint q1 q2) = ProductConstraint (substitute s q1) (substitute s q2)
  substitute s (EqualityConstraint t1 t2) = EqualityConstraint (substitute s t1) (substitute s t2)
  substitute s (TypeClassConstraint k ts) = TypeClassConstraint k $ fmap (substitute s) ts

instance Substitutable UniVar (Monotype UniVar) where
  substitute _ (VarType v) = VarType v
  substitute (Subst s) (UniType u) = HashMap.lookup u s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
  substitute s (FamilyApplyType k ts) = FamilyApplyType k $ fmap (substitute s) ts

instance Substitutable TypeVar (Monotype UniVar) where
  substitute _ (UniType v) = UniType v
  substitute (Subst s) (VarType v) = HashMap.lookup v s `fromJustOr` VarType v
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
  substitute s (FamilyApplyType k ts) = FamilyApplyType k $ fmap (substitute s) ts
