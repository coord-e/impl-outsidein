{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Simple.Type.Program
  ( typeProgram,
  )
where

import Control.Monad (unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Control.Monad.State (get, put, runStateT)
import Control.Monad.Trans (lift)
import qualified Data.HashMap.Strict as HashMap (elems, empty, insert, lookup)
import qualified Data.Vector as Vector (fromList)
import Data.Void (vacuous)
import Language.Simple.Extension (Extension, Generalizable (..))
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax
  ( Binding (..),
    Constraint (..),
    ExtensionConstraint,
    ExtensionMonotype,
    Monotype (..),
    Program (..),
    TermVar,
    TypeScheme (..),
  )
import Language.Simple.Type.Constraint (Fuv (..), GeneratedConstraint (..), UniVar)
import Language.Simple.Type.Env (HasLocalTypeEnv (..), HasProgramEnv, HasTypeEnv (..), runEnvT)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Generator (generateConstraint)
import Language.Simple.Type.Solver (solveConstraint)
import Language.Simple.Type.Substitution (Substitutable (..))
import Language.Simple.Util (logDocInfo)
import Prettyprinter (Pretty (..), nest, (<+>))

typeProgram ::
  forall x m.
  ( Extension x,
    MonadLogger m,
    MonadError (TypeError x) m
  ) =>
  Program x ->
  m ()
typeProgram Program {bindings, axioms, vars, dataCtors} = runEnvT axioms vars dataCtors $ foldr go (pure ()) bindings
  where
    go binding acc = do
      (x, s) <- typeBinding binding
      withTermVar x s acc

typeBinding ::
  ( Extension x,
    HasLocalTypeEnv x m,
    HasTypeEnv x m,
    HasProgramEnv x m,
    Fresh m,
    MonadLogger m,
    MonadError (TypeError x) m
  ) =>
  Binding x ->
  m (TermVar, TypeScheme x)
typeBinding (UnannotatedBinding x e) = do
  -- Generate
  a <- UniType <$> fresh
  (t, c) <- withLocalVar x a $ generateConstraint e
  -- Solve
  let c' = c <> Constraint (EqualityConstraint a t)
  let tch = fuv t <> fuv c'
  (q, u) <- solveConstraint mempty tch c'
  let t' = substitute u t
  -- Generalize
  s <- generalizeToTypeScheme q t'
  logDocInfo $ "typed unannotated binding" <+> pretty x <+> "::" <+> nest 2 (pretty s)
  pure (x, s)
typeBinding (AnnotatedBinding x s@ForallTypeScheme {constraint, monotype} e) = do
  -- Generate
  (v, c) <- withTermVar x s $ generateConstraint e
  -- Solve
  let tch = fuv v <> fuv c
  let c' = c <> Constraint (EqualityConstraint v (vacuous monotype))
  (q, _) <- solveConstraint (vacuous constraint) tch c'
  unless (isEmpty q) $ throwError (UnresolvedConstraint q)
  logDocInfo $ "typed annotated binding" <+> pretty x <+> "::" <+> nest 2 (pretty s)
  pure (x, s)
  where
    isEmpty EmptyConstraint = True
    isEmpty _ = False

generalizeToTypeScheme ::
  ( Generalizable x (ExtensionMonotype x),
    Generalizable x (ExtensionConstraint x),
    Fresh m
  ) =>
  Constraint x UniVar ->
  Monotype x UniVar ->
  m (TypeScheme x)
generalizeToTypeScheme q t = do
  ((constraint, monotype), vars) <- flip runStateT HashMap.empty $ do
    q' <- generalize gen q
    t' <- generalize gen t
    pure (q', t')
  pure
    ForallTypeScheme
      { vars = Vector.fromList $ HashMap.elems vars,
        constraint,
        monotype
      }
  where
    gen u = do
      m <- get
      case HashMap.lookup u m of
        Just v -> pure $ VarType v
        Nothing -> do
          v <- lift fresh
          put $ HashMap.insert u v m
          pure $ VarType v
