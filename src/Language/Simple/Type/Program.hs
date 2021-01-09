{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Simple.Type.Program
  ( typeProgram,
  )
where

import Control.Monad (unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Control.Monad.State (runStateT, state)
import qualified Data.HashMap.Strict as HashMap (elems, empty, insert, lookup, size)
import Data.Text (Text, pack)
import qualified Data.Vector as Vector (fromList)
import Data.Void (Void, vacuous)
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax
  ( Binding (..),
    Constraint (..),
    Monotype (..),
    Program (..),
    SimpleMonotype,
    TermVar,
    TypeScheme (..),
    TypeVar (..),
  )
import Language.Simple.Type.Constraint (Fuv (..), GeneratedConstraint (..), UniVar, isEmpty)
import Language.Simple.Type.Env (HasLocalTypeEnv (..), HasProgramEnv, HasTypeEnv (..), runBuiltinT, runEnvT)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Generator (generateConstraint)
import Language.Simple.Type.Solver (solveConstraint)
import Language.Simple.Type.Substitution (Substitutable (..))
import Numeric (showIntAtBase)
import Prettyprinter (Pretty (..), nest, (<+>))
import Util (logDocInfo)

typeProgram ::
  ( MonadLogger m,
    MonadError TypeError m
  ) =>
  Program ->
  m ()
typeProgram Program {bindings, axioms, vars, dataCtors} =
  runEnvT axioms vars dataCtors . runBuiltinT $ foldr go (pure ()) bindings
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
  let c' = c <> Constraint (EqualityConstraint a t)
  let tch = fuv t <> fuv c'
  (q, u) <- solveConstraint mempty tch c'
  let t' = substitute u t
  unless (isEmpty q || not (null (fuv q))) $ throwError (UnresolvedConstraint q)
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

generalizeToTypeScheme ::
  Monad m =>
  Constraint UniVar ->
  Monotype UniVar ->
  m TypeScheme
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
    gen = state . f
    f u m =
      case HashMap.lookup u m of
        Just v -> (VarType v, m)
        Nothing -> (VarType v, HashMap.insert u v m)
          where
            v = nextVar m
    nextVar = TypeVar . intToName . HashMap.size

intToName :: Int -> Text
intToName i = pack str
  where
    str = showIntAtBase base (chars !!) i ""
    base = toEnum (length chars)
    chars = ['a' .. 'z']

class Generalizable f where
  generalize :: Applicative m => (UniVar -> m SimpleMonotype) -> f UniVar -> m (f Void)

instance Generalizable Monotype where
  generalize f (UniType u) = f u
  generalize _ (VarType v) = pure $ VarType v
  generalize f (ApplyType k ts) = ApplyType k <$> traverse (generalize f) ts
  generalize f (FamilyApplyType k ts) = FamilyApplyType k <$> traverse (generalize f) ts

instance Generalizable Constraint where
  generalize _ EmptyConstraint = pure EmptyConstraint
  generalize f (ProductConstraint q1 q2) = ProductConstraint <$> generalize f q1 <*> generalize f q2
  generalize f (EqualityConstraint t1 t2) = EqualityConstraint <$> generalize f t1 <*> generalize f t2
  generalize f (TypeClassConstraint k ts) = TypeClassConstraint k <$> traverse (generalize f) ts
