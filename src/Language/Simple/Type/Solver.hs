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
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (toList)
import Language.Simple.Extension (Extension (..))
import Language.Simple.Syntax (Constraint (..))
import Language.Simple.Type.Constraint (GeneratedConstraint (..), UniVar, implic, reduce, simple)
import Language.Simple.Type.Env (HasProgramEnv)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Substitutable (..), Unifier)
import Language.Simple.Util (logParamsDebug)
import Prettyprinter (Pretty (..))

solveConstraint ::
  ( Extension x,
    HasProgramEnv x m,
    MonadLogger m,
    MonadError (TypeError x) m
  ) =>
  Constraint x UniVar ->
  HashSet UniVar ->
  GeneratedConstraint x ->
  m (Constraint x UniVar, Unifier x)
solveConstraint given tch wanted = do
  (residual, unifier) <- simplifyConstraint given tch (simple wanted)
  let residual' = reduce residual
  forM_ (implic (substitute unifier wanted)) $ \(vars, premise, c) -> do
    (q, _) <- solveConstraint (given <> residual' <> premise) vars c
    unless (isEmpty q) $ throwError (UnresolvedConstraint q)
  logParamsDebug
    "solveConstraint"
    [ ("given", pretty given),
      ("tch", pretty (HashSet.toList tch)),
      ("wanted", pretty wanted),
      ("(out) residual", pretty residual'),
      ("(out) unifier", pretty unifier)
    ]
  pure (residual', unifier)
  where
    isEmpty EmptyConstraint = True
    isEmpty _ = False
