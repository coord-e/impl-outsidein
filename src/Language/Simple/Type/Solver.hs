{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Language.Simple.Type.Solver (solveConstraint) where

import Control.Monad (forM_, unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import qualified Data.HashMap.Strict as HashMap (foldrWithKey, lookup)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (delete, member, toList)
import Data.Hashable (Hashable)
import qualified Data.Vector as Vector (zip)
import GHC.Generics (Generic)
import Language.Simple.Syntax (Constraint (..), Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (GeneratedConstraint (..), UniVar, implic, reduce, simple)
import Language.Simple.Type.Env (HasProgramEnv)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Subst (..), Substitutable (..), Unifier)
import qualified Language.Simple.Type.Substitution as Subst (compose, empty, singleton)
import Language.Simple.Util (fromJustOr, logParamsDebug)
import Prettyprinter (pretty)

solveConstraint ::
  ( HasProgramEnv m,
    MonadLogger m,
    MonadError TypeError m
  ) =>
  Constraint UniVar ->
  HashSet UniVar ->
  GeneratedConstraint ->
  m (Constraint UniVar, Unifier)
solveConstraint given tch wanted = do
  logParamsDebug
    "solveConstraint"
    [ ("given", pretty given),
      ("tch", pretty (HashSet.toList tch)),
      ("wanted", pretty wanted)
    ]
  (residual, unifier) <- simplifyConstraint given tch (simple wanted)
  let residual' = reduce residual
  forM_ (implic (substitute unifier wanted)) $ \(vars, premise, c) -> do
    (q, _) <- solveConstraint (given <> residual' <> premise) vars c
    unless (isEmpty q) $ throwError (UnresolvedConstraint q)
  pure (residual', unifier)
  where
    isEmpty EmptyConstraint = True
    isEmpty _ = False

data SomeVar
  = UniSomeVar UniVar
  | RigidSomeVar TypeVar
  deriving stock (Show, Ord, Eq, Generic)
  deriving anyclass (Hashable)

instance Substitutable SomeVar GeneratedConstraint where
  substitute s (Constraint q) = Constraint (substitute s q)
  substitute s (ProductGeneratedConstraint c1 c2) = ProductGeneratedConstraint (substitute s c1) (substitute s c2)
  substitute s@(Subst m) (ExistentialGeneratedConstraint vs p c) = ExistentialGeneratedConstraint vs' (substitute s p) (substitute s c)
    where
      vs' = HashMap.foldrWithKey go vs m
      go (UniSomeVar u) _ = HashSet.delete u
      go _ _ = id

instance Substitutable SomeVar (Constraint UniVar) where
  substitute _ EmptyConstraint = EmptyConstraint
  substitute s (ProductConstraint q1 q2) = ProductConstraint (substitute s q1) (substitute s q2)
  substitute s (EqualityConstraint t1 t2) = EqualityConstraint (substitute s t1) (substitute s t2)

instance Substitutable SomeVar (Monotype UniVar) where
  substitute (Subst s) (VarType v) = HashMap.lookup (RigidSomeVar v) s `fromJustOr` VarType v
  substitute (Subst s) (UniType u) = HashMap.lookup (UniSomeVar u) s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts

simplifyConstraint ::
  ( HasProgramEnv m,
    MonadError TypeError m
  ) =>
  Constraint UniVar ->
  HashSet UniVar ->
  Constraint UniVar ->
  m (Constraint UniVar, Unifier)
simplifyConstraint given tch wanted = pure . solve $ substitute givenSubst wanted
  where
    givenSubst = reduceGiven given
    reduceGiven EmptyConstraint = Subst.empty
    reduceGiven (EqualityConstraint t1 t2) = unifyGiven t1 t2
    reduceGiven (ProductConstraint q1 q2) = Subst.compose s2 s1
      where
        s1 = reduceGiven q1
        s2 = reduceGiven (substitute s1 q2)
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
