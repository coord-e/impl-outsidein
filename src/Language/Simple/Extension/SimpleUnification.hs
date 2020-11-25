{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Simple.Extension.SimpleUnification
  ( SimpleUnification,
    simplifyUnificationConstraint,
    toXConstraint,
    toXType,
  )
where

import Control.Applicative (empty)
import qualified Data.HashMap.Strict as HashMap (foldrWithKey, lookup)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (delete, member)
import Data.Hashable (Hashable)
import qualified Data.Vector as Vector (zip)
import GHC.Generics (Generic)
import Language.Simple.Extension
  ( Extension (..),
    ExtensionConstraint,
    ExtensionMonotype,
    ExtensionTypeError,
    Generalizable (..),
    Instantiable (..),
    SyntaxExtension (..),
  )
import Language.Simple.Syntax (Constraint (..), Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (Fuv (..), GeneratedConstraint (..), UniVar)
import Language.Simple.Type.Substitution (Subst (..), Substitutable (..), Unifier)
import qualified Language.Simple.Type.Substitution as Subst (compose, empty, singleton)
import Language.Simple.Util (fromJustOr)
import Prettyprinter (Pretty (..))

data SimpleUnification

type X = SimpleUnification

data instance ExtensionMonotype X a

-- hlint can't parse EmptyCase without {}
{- ORMOLU_DISABLE -}
discardMonotypeExt :: ExtensionMonotype X a -> b
discardMonotypeExt x = case x of {}
{- ORMOLU_ENABLE -}

instance Functor (ExtensionMonotype X) where
  fmap _ = discardMonotypeExt

instance Fuv (ExtensionMonotype X a) where
  fuv = discardMonotypeExt

instance Pretty (ExtensionMonotype X a) where
  pretty = discardMonotypeExt

instance Generalizable X (ExtensionMonotype X) where
  generalize _ = discardMonotypeExt

instance Instantiable X (ExtensionMonotype X) where
  instantiate _ = discardMonotypeExt

instance Substitutable X UniVar (ExtensionMonotype X a) where
  substitute _ = discardMonotypeExt

instance SyntaxExtension X (ExtensionMonotype X) where
  extensionParser = empty

data instance ExtensionConstraint X a

-- ditto
{- ORMOLU_DISABLE -}
discardConstraintExt :: ExtensionConstraint X a -> b
discardConstraintExt x = case x of {}
{- ORMOLU_ENABLE -}

instance Functor (ExtensionConstraint X) where
  fmap _ = discardConstraintExt

instance Fuv (ExtensionConstraint X a) where
  fuv = discardConstraintExt

instance Pretty (ExtensionConstraint X a) where
  pretty = discardConstraintExt

instance Generalizable X (ExtensionConstraint X) where
  generalize _ = discardConstraintExt

instance Instantiable X (ExtensionConstraint X) where
  instantiate _ = discardConstraintExt

instance Substitutable X UniVar (ExtensionConstraint X a) where
  substitute _ = discardConstraintExt

instance SyntaxExtension X (ExtensionConstraint X) where
  extensionParser = empty

data instance ExtensionTypeError X

-- ditto
{- ORMOLU_DISABLE -}
instance Pretty (ExtensionTypeError X) where
  pretty x = case x of {}
{- ORMOLU_ENABLE -}

instance Extension X where
  simplifyConstraint given tch wanted = pure $ simplifyUnificationConstraint given tch wanted

simplifyUnificationConstraint ::
  Constraint X UniVar ->
  HashSet UniVar ->
  Constraint X UniVar ->
  (Constraint X UniVar, Unifier X)
simplifyUnificationConstraint given tch wanted = solve $ substitute givenSubst wanted
  where
    givenSubst = reduceGiven given
    reduceGiven EmptyConstraint = Subst.empty
    reduceGiven (EqualityConstraint t1 t2) = unifyGiven t1 t2
    reduceGiven (ProductConstraint q1 q2) = Subst.compose s2 s1
      where
        s1 = reduceGiven q1
        s2 = reduceGiven (substitute s1 q2)
    reduceGiven (ExtensionConstraint x) = discardConstraintExt x
    unifyGiven (UniType u) t = Subst.singleton (UniSomeVar u) t
    unifyGiven t (UniType u) = Subst.singleton (UniSomeVar u) t
    unifyGiven (VarType v) t = Subst.singleton (RigidSomeVar v) t
    unifyGiven t (VarType v) = Subst.singleton (RigidSomeVar v) t
    unifyGiven (ApplyType k1 ts1) (ApplyType k2 ts2) | k1 == k2 = unifyGivenAll ts1 ts2
    unifyGiven _ _ = Subst.empty
    unifyGivenAll xs ys = foldr go Subst.empty (Vector.zip xs ys)
      where
        go (x, y) s1 =
          let s2 = unifyGiven (substitute s1 x) (substitute s1 y)
           in Subst.compose s2 s1
    solve EmptyConstraint = (mempty, Subst.empty)
    solve (EqualityConstraint t1 t2) = unify t1 t2
    solve (ProductConstraint q1 q2) = (substitute s2 r1 <> r2, Subst.compose s2 s1)
      where
        (r1, s1) = solve q1
        (r2, s2) = solve (substitute s1 q2)
    unify (UniType u1) (UniType u2) | u1 == u2 = (mempty, Subst.empty)
    unify (VarType v1) (VarType v2) | v1 == v2 = (mempty, Subst.empty)
    unify (UniType u) t | HashSet.member u tch = (mempty, Subst.singleton u t)
    unify t (UniType u) | HashSet.member u tch = (mempty, Subst.singleton u t)
    unify (ApplyType k1 ts1) (ApplyType k2 ts2) | k1 == k2 = unifyAll ts1 ts2
    unify t1 t2 = (EqualityConstraint t1 t2, Subst.empty)
    unifyAll xs ys = foldr go (mempty, Subst.empty) (Vector.zip xs ys)
      where
        go (x, y) (c, s1) =
          let (r, s2) = unify (substitute s1 x) (substitute s1 y)
           in (c <> r, Subst.compose s2 s1)

data SomeVar
  = UniSomeVar UniVar
  | RigidSomeVar TypeVar
  deriving stock (Show, Ord, Eq, Generic)
  deriving anyclass (Hashable)

instance Substitutable X SomeVar (GeneratedConstraint X) where
  substitute s (Constraint q) = Constraint (substitute s q)
  substitute s (ProductGeneratedConstraint c1 c2) = ProductGeneratedConstraint (substitute s c1) (substitute s c2)
  substitute s@(Subst m) (ExistentialGeneratedConstraint vs p c) = ExistentialGeneratedConstraint vs' (substitute s p) (substitute s c)
    where
      vs' = HashMap.foldrWithKey go vs m
      go (UniSomeVar u) _ = HashSet.delete u
      go _ _ = id

instance Substitutable X SomeVar (Constraint X UniVar) where
  substitute _ EmptyConstraint = EmptyConstraint
  substitute s (ProductConstraint q1 q2) = ProductConstraint (substitute s q1) (substitute s q2)
  substitute s (EqualityConstraint t1 t2) = EqualityConstraint (substitute s t1) (substitute s t2)

instance Substitutable X SomeVar (Monotype X UniVar) where
  substitute (Subst s) (VarType v) = HashMap.lookup (RigidSomeVar v) s `fromJustOr` VarType v
  substitute (Subst s) (UniType u) = HashMap.lookup (UniSomeVar u) s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts

toXConstraint :: Constraint X a -> Constraint x a
toXConstraint EmptyConstraint = EmptyConstraint
toXConstraint (ProductConstraint q1 q2) = ProductConstraint (toXConstraint q1) (toXConstraint q2)
toXConstraint (EqualityConstraint t1 t2) = EqualityConstraint (toXType t1) (toXType t2)

toXType :: Monotype X a -> Monotype x a
toXType (VarType v) = VarType v
toXType (UniType u) = UniType u
toXType (ApplyType k ts) = ApplyType k $ fmap toXType ts
