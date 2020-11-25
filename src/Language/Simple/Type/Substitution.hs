{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Simple.Type.Substitution
  ( Subst (..),
    limit,
    compose,
    domain,
    null,
    lookup,
    empty,
    member,
    singleton,
    replace,
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
import qualified Data.HashSet as HashSet (difference, toMap)
import Data.Hashable (Hashable)
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax (Constraint (..), ExtensionConstraint, ExtensionMonotype, Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (GeneratedConstraint (..), UniVar)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Util (fromJustOr, orThrow)
import Prettyprinter (Pretty (..), list, (<+>))
import Prelude hiding (lookup, null)

newtype Subst x a = Subst (HashMap a (Monotype x UniVar))

type Unifier x = Subst x UniVar

type Instantiator x = Subst x TypeVar

instance (Pretty (ExtensionMonotype x UniVar), Pretty a) => Pretty (Subst x a) where
  pretty (Subst m) = list . map f $ HashMap.toList m
    where
      f (k, v) = pretty k <+> "↦" <+> pretty v

empty :: Subst x a
empty = Subst HashMap.empty

null :: Subst x a -> Bool
null (Subst m) = HashMap.null m

member :: (Hashable a, Eq a) => a -> Subst x a -> Bool
member k (Subst m) = HashMap.member k m

lookup :: (Hashable a, Eq a) => a -> Subst x a -> Maybe (Monotype x UniVar)
lookup k (Subst m) = HashMap.lookup k m

domain :: Subst x a -> HashSet a
domain (Subst m) = HashMap.keysSet m

limit :: (Hashable a, Eq a) => HashSet a -> Subst x a -> Subst x a
limit s (Subst m) = Subst . HashMap.intersection m $ HashSet.toMap s

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

replace :: MonadError (TypeError x) m => Instantiator x -> TypeVar -> m (Monotype x UniVar)
replace m v = lookup v m `orThrow` UnboundTypeVar v

fromBinders :: (Fresh m, Foldable f) => f TypeVar -> m (Instantiator x)
fromBinders = foldlM go empty
  where
    go (Subst subst) v = do
      a <- fresh
      pure . Subst $ HashMap.insert v (UniType a) subst

class Substitutable x a b | a b -> x where
  substitute :: Subst x a -> b -> b

instance Substitutable x UniVar (Constraint x UniVar) => Substitutable x UniVar (GeneratedConstraint x) where
  substitute s (Constraint q) = Constraint (substitute s q)
  substitute s (ProductGeneratedConstraint c1 c2) = ProductGeneratedConstraint (substitute s c1) (substitute s c2)
  substitute s@(Subst m) (ExistentialGeneratedConstraint vs p c) = ExistentialGeneratedConstraint vs' (substitute s p) (substitute s c)
    where
      vs' = HashSet.difference vs (HashMap.keysSet m)

instance
  ( Substitutable x a (ExtensionConstraint x UniVar),
    Substitutable x a (Monotype x UniVar)
  ) =>
  Substitutable x a (Constraint x UniVar)
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

instance Substitutable x TypeVar (ExtensionMonotype x UniVar) => Substitutable x TypeVar (Monotype x UniVar) where
  substitute _ (UniType v) = UniType v
  substitute (Subst s) (VarType v) = HashMap.lookup v s `fromJustOr` VarType v
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
  substitute s (ExtensionType x) = ExtensionType $ substitute s x
