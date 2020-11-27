{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Simple.ConstraintDomain.SimpleUnification
  ( SimpleUnification,
    ExtensionTypeError (..),
    simplifyUnificationConstraint,
    toXConstraint,
    toXType,
  )
where

import Control.Applicative (empty)
import Control.Monad.Except (MonadError (..))
import Data.Foldable (foldrM)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (member)
import qualified Data.Vector as Vector (zip)
import Language.Simple.ConstraintDomain
  ( ConstraintDomain (..),
    ExtensionConstraint,
    ExtensionMonotype,
    ExtensionTypeError,
    Generalizable (..),
    Instantiable (..),
    SyntaxExtension (..),
  )
import Language.Simple.ConstraintDomain.Util (Ftv (..), Tv (..), pattern TvType)
import Language.Simple.Syntax (Constraint (..), Monotype (..))
import Language.Simple.Type.Constraint (Fuv (..), UniVar)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Substitutable (..), Unifier)
import qualified Language.Simple.Type.Substitution as Subst (compose, empty, singleton)
import Prettyprinter (Pretty (..), squotes, (<+>))

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

instance Ftv (ExtensionMonotype X a) where
  ftv = discardMonotypeExt

instance Pretty (ExtensionMonotype X a) where
  pretty = discardMonotypeExt

instance Generalizable X (ExtensionMonotype X) where
  generalize _ = discardMonotypeExt

instance Instantiable X (ExtensionMonotype X) where
  instantiate _ = discardMonotypeExt

instance Substitutable X UniVar (ExtensionMonotype X a) where
  substitute _ = discardMonotypeExt

instance Substitutable X Tv (ExtensionMonotype X a) where
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

instance Ftv (ExtensionConstraint X a) where
  ftv = discardConstraintExt

instance Pretty (ExtensionConstraint X a) where
  pretty = discardConstraintExt

instance Generalizable X (ExtensionConstraint X) where
  generalize _ = discardConstraintExt

instance Instantiable X (ExtensionConstraint X) where
  instantiate _ = discardConstraintExt

instance Substitutable X UniVar (ExtensionConstraint X a) where
  substitute _ = discardConstraintExt

instance Substitutable X Tv (ExtensionConstraint X a) where
  substitute _ = discardConstraintExt

instance SyntaxExtension X (ExtensionConstraint X) where
  extensionParser = empty

data instance ExtensionTypeError X
  = OccurCheckError Tv (Monotype X UniVar)
  | MismatchedTypes (Monotype X UniVar) (Monotype X UniVar)

instance Pretty (ExtensionTypeError X) where
  pretty (OccurCheckError v t) = "occur check failed:" <+> pretty v <+> "~" <+> pretty t
  pretty (MismatchedTypes t1 t2) =
    "could not match expected type"
      <+> squotes (pretty t1)
      <+> "with actual type"
      <+> squotes (pretty t2)

instance ConstraintDomain X where
  simplifyConstraint given tch wanted = reinterpretError $ simplifyUnificationConstraint given tch wanted
    where
      reinterpretError (Right x) = pure x
      reinterpretError (Left e) = throwError (ExtensionTypeError e)

simplifyUnificationConstraint ::
  MonadError (ExtensionTypeError X) m =>
  Constraint X UniVar ->
  HashSet UniVar ->
  Constraint X UniVar ->
  m (Constraint X UniVar, Unifier X)
simplifyUnificationConstraint given tch wanted = do
  givenSubst <- reduceGiven given
  solve $ substitute givenSubst wanted
  where
    reduceGiven EmptyConstraint = pure Subst.empty
    reduceGiven (EqualityConstraint t1 t2) = unifyGiven t1 t2
    reduceGiven (ProductConstraint q1 q2) = do
      s1 <- reduceGiven q1
      s2 <- reduceGiven (substitute s1 q2)
      pure $ Subst.compose s2 s1
    reduceGiven (ExtensionConstraint x) = discardConstraintExt x
    unifyGiven (TvType v) t = unifyVarGiven v t
    unifyGiven t (TvType v) = unifyVarGiven v t
    unifyGiven t1@(ApplyType k1 ts1) t2@(ApplyType k2 ts2)
      | k1 == k2 && length ts1 == length ts2 = unifyGivenAll ts1 ts2
      | otherwise = throwError $ MismatchedTypes t1 t2
    unifyGivenAll xs ys = foldrM go Subst.empty (Vector.zip xs ys)
      where
        go (x, y) s1 = do
          s2 <- unifyGiven (substitute s1 x) (substitute s1 y)
          pure $ Subst.compose s2 s1
    unifyVarGiven v t
      | HashSet.member v (ftv t) = throwError $ OccurCheckError v t
      | otherwise = pure $ Subst.singleton v t
    solve EmptyConstraint = pure (mempty, Subst.empty)
    solve (EqualityConstraint t1 t2) = unify t1 t2
    solve (ProductConstraint q1 q2) = do
      (r1, s1) <- solve q1
      (r2, s2) <- solve (substitute s1 q2)
      pure (substitute s2 r1 <> r2, Subst.compose s2 s1)
    unify (TvType v1) (TvType v2) | v1 == v2 = pure (mempty, Subst.empty)
    unify (UniType u) t = unifyVar u t
    unify t (UniType u) = unifyVar u t
    unify t1@(ApplyType k1 ts1) t2@(ApplyType k2 ts2)
      | k1 == k2 && length ts1 == length ts2 = unifyAll ts1 ts2
      | otherwise = throwError $ MismatchedTypes t1 t2
    unify t1 t2 = pure (EqualityConstraint t1 t2, Subst.empty)
    unifyVar u t
      | HashSet.member u (fuv t) = throwError $ OccurCheckError (UniTv u) t
      | HashSet.member u tch = pure (mempty, Subst.singleton u t)
      | otherwise = pure (EqualityConstraint (UniType u) t, Subst.empty)
    unifyAll xs ys = foldrM go (mempty, Subst.empty) (Vector.zip xs ys)
      where
        go (x, y) (c, s1) = do
          (r, s2) <- unify (substitute s1 x) (substitute s1 y)
          pure (c <> r, Subst.compose s2 s1)

toXConstraint :: Constraint X a -> Constraint x a
toXConstraint EmptyConstraint = EmptyConstraint
toXConstraint (ProductConstraint q1 q2) = ProductConstraint (toXConstraint q1) (toXConstraint q2)
toXConstraint (EqualityConstraint t1 t2) = EqualityConstraint (toXType t1) (toXType t2)

toXType :: Monotype X a -> Monotype x a
toXType (VarType v) = VarType v
toXType (UniType u) = UniType u
toXType (ApplyType k ts) = ApplyType k $ fmap toXType ts
