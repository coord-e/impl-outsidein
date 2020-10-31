{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Simple.Type.Program (typeProgram) where

import Control.Monad (unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Control.Monad.State (get, put, runStateT)
import Control.Monad.Trans (lift)
import qualified Data.HashMap.Strict as HashMap (elems, empty, insert, lookup)
import qualified Data.Vector as Vector (fromList)
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax
  ( Binding (..),
    Constraint (..),
    Monotype (..),
    Program (..),
    TermVar,
    TypeScheme (..),
    upgradeConstraint,
    upgradeMonotype,
  )
import Language.Simple.Type.Constraint (GeneratedConstraint (..), UniVar, fuv)
import Language.Simple.Type.Env (HasLocalTypeEnv (..), HasProgramEnv, HasTypeEnv (..), runEnvT)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Generator (generateConstraint)
import Language.Simple.Type.Solver (solveConstraint)
import Language.Simple.Type.Substitution (substitute)
import Language.Simple.Util (logDocInfo)
import Prettyprinter (nest, pretty, (<+>))

typeProgram :: (MonadLogger m, MonadError TypeError m) => Program -> m ()
typeProgram Program {bindings, axioms, dataCtors} = runEnvT axioms dataCtors $ foldr go (pure ()) bindings
  where
    go binding acc = do
      (x, s) <- typeBinding binding
      withTermVar x s acc

typeBinding ::
  ( HasLocalTypeEnv m,
    HasTypeEnv m,
    HasProgramEnv m,
    Fresh m,
    MonadLogger m,
    MonadError TypeError m
  ) =>
  Binding ->
  m (TermVar, TypeScheme)
typeBinding (UnannotatedBinding x e) = do
  -- Generate
  a <- UniType <$> fresh
  (t, c) <- withLocalVar x a $ generateConstraint e
  -- Solve
  let tch = fuv t <> fuv c
  let c' = c <> Constraint (EqualityConstraint a t)
  (q, u) <- solveConstraint mempty tch c'
  let t' = substitute u t
  -- Generalize
  s <- generalize q t'
  logDocInfo $ "typed unannotated binding" <+> pretty x <+> "::" <+> nest 2 (pretty s)
  pure (x, s)
typeBinding (AnnotatedBinding x s@ForallTypeScheme {constraint, monotype} e) = do
  -- Generate
  (v, c) <- withTermVar x s $ generateConstraint e
  -- Solve
  let tch = fuv v <> fuv c
  let c' = c <> Constraint (EqualityConstraint v (upgradeMonotype monotype))
  (q, _) <- solveConstraint (upgradeConstraint constraint) tch c'
  unless (isEmpty q) $ throwError (UnresolvedConstraint q)
  logDocInfo $ "typed annotated binding" <+> pretty x <+> "::" <+> nest 2 (pretty s)
  pure (x, s)
  where
    isEmpty EmptyConstraint = True
    isEmpty _ = False

generalize :: Fresh m => Constraint UniVar -> Monotype UniVar -> m TypeScheme
generalize q t = do
  ((constraint, monotype), vars) <- runStateT gen HashMap.empty
  pure
    ForallTypeScheme
      { vars = Vector.fromList $ HashMap.elems vars,
        constraint,
        monotype
      }
  where
    gen = do
      q' <- genConstraint q
      t' <- genMonotype t
      pure (q', t')
    genConstraint EmptyConstraint = pure EmptyConstraint
    genConstraint (ProductConstraint q1 q2) = ProductConstraint <$> genConstraint q1 <*> genConstraint q2
    genConstraint (EqualityConstraint t1 t2) = EqualityConstraint <$> genMonotype t1 <*> genMonotype t2
    genMonotype (UniType u) = do
      m <- get
      case HashMap.lookup u m of
        Just v -> pure $ VarType v
        Nothing -> do
          v <- lift fresh
          put $ HashMap.insert u v m
          pure $ VarType v
    genMonotype (VarType v) = pure $ VarType v
    genMonotype (ApplyType k ts) = ApplyType k <$> mapM genMonotype ts
