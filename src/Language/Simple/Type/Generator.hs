{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Simple.Type.Generator
  ( generateConstraint,
  )
where

import Control.Monad (unless, when)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Data.Foldable (foldlM)
import qualified Data.HashMap.Strict as HashMap (insert, intersection, keys, member, union)
import qualified Data.HashSet as HashSet (delete, difference, union)
import qualified Data.Vector as Vector (length, zip)
import Data.Void (Void, vacuous)
import Language.Simple.Fresh (Fresh (..), GenFresh)
import Language.Simple.Syntax
  ( CaseArm (..),
    Constraint (..),
    DataCtor,
    DataCtorType (..),
    Expr (..),
    Monotype (..),
    SimpleConstraint,
    SimpleMonotype,
    TermVar,
    TypeScheme (..),
    TypeVar,
    functionType,
  )
import Language.Simple.Type.Constraint (Fuv (..), GeneratedConstraint (..), UniVar)
import Language.Simple.Type.Env (HasLocalTypeEnv (..), HasProgramEnv (..), HasTypeEnv (..))
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Instantiator, Subst (..))
import qualified Language.Simple.Type.Substitution as Subst (replaceAll)
import Util (foldMapM, orThrowM)

generateConstraint ::
  ( HasLocalTypeEnv m,
    HasTypeEnv m,
    HasProgramEnv m,
    MonadLogger m,
    Fresh m,
    MonadError TypeError m
  ) =>
  Expr ->
  m (Monotype UniVar, GeneratedConstraint)
generateConstraint (CtorExpr k) = do
  d <- findDataCtor k
  (t, q) <- instantiateTypeScheme $ dataCtorTypeToTypeScheme d
  pure (t, Constraint q)
generateConstraint (VarExpr x) =
  lookupLocalVar x >>= \case
    Just t -> pure (t, Constraint EmptyConstraint)
    Nothing -> do
      s <- findTermVar x
      (t, q) <- instantiateTypeScheme s
      pure (t, Constraint q)
generateConstraint (LambdaExpr x e) = do
  a <- UniType <$> fresh
  (t, c) <- withLocalVar x a $ generateConstraint e
  pure (functionType a t, c)
generateConstraint (ApplyExpr e1 e2) = do
  (t1, c1) <- generateConstraint e1
  (t2, c2) <- generateConstraint e2
  a <- UniType <$> fresh
  pure (a, c1 <> c2 <> Constraint (EqualityConstraint t1 (functionType t2 a)))
generateConstraint (CaseExpr e arms) = do
  (t, c) <- generateConstraint e
  ret <- UniType <$> fresh
  cArms <- foldMapM (generateForArm t ret) arms
  pure (ret, c <> cArms)
  where
    withLocalVars xs ts m = foldr (uncurry withLocalVar) m $ Vector.zip xs ts
    isGADT exs EmptyConstraint | null exs = False
    isGADT _ _ = True
    generateForArm tScrutinee tCase CaseArm {ctor = k, vars, body} = do
      DataCtorType {universalVars, existentialVars, constraint, fields, ctor, ctorArgs} <- findDataCtor k
      -- instantiate data constructor type
      (universalSubst, universalUniVars) <- fromBinders UniType universalVars
      (existentialSubst, _) <- fromBinders VarType existentialVars
      subst <- composeInstantiator universalSubst existentialSubst
      constraint' <- instantiateConstraint subst constraint
      fields' <- mapM (instantiateMonotype subst) fields
      ctorArgs' <- mapM (instantiateMonotype subst . VarType) ctorArgs
      -- generate constraints from arm body
      unless (Vector.length vars == Vector.length fields) $
        throwError MismatchedNumberOfDataCtorFields {ctor = k, expected = Vector.length fields, got = Vector.length vars}
      (tBody, cBody) <- withLocalVars vars fields' $ generateConstraint body
      -- calculate \( \delta \)
      envFuv <- localEnvFuv
      let delta' = (fuv tBody <> fuv cBody) `HashSet.difference` envFuv
      let delta = foldr HashSet.delete delta' universalUniVars
      -- produce final constraint \( C'_i \)
      let cArm =
            cBody
              <> Constraint (EqualityConstraint tBody tCase)
      let cScrutinee = Constraint (EqualityConstraint (ApplyType ctor ctorArgs') tScrutinee)
      if isGADT existentialVars constraint
        then pure $ ExistentialGeneratedConstraint delta constraint' cArm <> cScrutinee
        else pure $ cArm <> cScrutinee
generateConstraint (UnannotatedLetExpr x e1 e2) = do
  (t1, c1) <- generateConstraint e1
  (t2, c2) <- withLocalVar x t1 $ generateConstraint e2
  pure (t2, c1 <> c2)
generateConstraint (AnnotatedLetExpr x s e1 e2)
  | isMono s = generateForMono
  | otherwise = generateForPoly
  where
    isMono ForallTypeScheme {vars, constraint = EmptyConstraint} | null vars = True
    isMono _ = False
    generateForMono = do
      (t1, c1) <- generateConstraint e1
      (t2, c2) <- withTermVar x s $ generateConstraint e2
      (monotype, _) <- instantiateTypeScheme s
      pure (t2, c1 <> c2 <> Constraint (EqualityConstraint t1 monotype))
    generateForPoly = do
      (t1, c1) <- generateConstraint e1
      (t2, c2) <- withTermVar x s $ generateConstraint e2
      let ForallTypeScheme {constraint, monotype} = s
      envFuv <- localEnvFuv
      let delta = (fuv t1 `HashSet.union` fuv c1) `HashSet.difference` envFuv
      let c = c1 <> Constraint (EqualityConstraint t1 (vacuous monotype))
      pure (t2, c2 <> ExistentialGeneratedConstraint delta (vacuous constraint) c)

dataCtorTypeToTypeScheme :: DataCtorType -> TypeScheme
dataCtorTypeToTypeScheme DataCtorType {universalVars, existentialVars, constraint, fields, ctor, ctorArgs} =
  ForallTypeScheme {vars, constraint, monotype}
  where
    vars = universalVars <> existentialVars
    monotype = foldr functionType ret fields
    ret = ApplyType ctor (fmap VarType ctorArgs)

instantiateTypeScheme ::
  ( Fresh m,
    MonadError TypeError m
  ) =>
  TypeScheme ->
  m (Monotype UniVar, Constraint UniVar)
instantiateTypeScheme ForallTypeScheme {vars, constraint, monotype} = do
  (subst, _) <- fromBinders UniType vars
  q <- instantiateConstraint subst constraint
  t <- instantiateMonotype subst monotype
  pure (t, q)

fromBinders ::
  ( Foldable t,
    Fresh m,
    GenFresh a,
    MonadError TypeError m
  ) =>
  (a -> Monotype UniVar) ->
  t TypeVar ->
  m (Instantiator, [a])
fromBinders toMonotype = fmap g . foldlM f (mempty, [])
  where
    f (subst, vars) v = do
      when (HashMap.member v subst) $ throwError (ConflictingTypeVars v)
      a <- fresh
      pure (HashMap.insert v (toMonotype a) subst, a : vars)
    g (subst, vars) = (Subst subst, vars)

composeInstantiator :: MonadError TypeError m => Instantiator -> Instantiator -> m Instantiator
composeInstantiator (Subst m1) (Subst m2)
  | null intersection = pure . Subst $ HashMap.union m1 m2
  | otherwise = throwError . ConflictingTypeVars . head $ HashMap.keys intersection
  where
    intersection = HashMap.intersection m1 m2

instantiateMonotype ::
  MonadError TypeError m =>
  Instantiator ->
  SimpleMonotype ->
  m (Monotype UniVar)
instantiateMonotype = instantiate . Subst.replaceAll

instantiateConstraint ::
  ( MonadError TypeError m
  ) =>
  Instantiator ->
  SimpleConstraint ->
  m (Constraint UniVar)
instantiateConstraint = instantiate . Subst.replaceAll

findDataCtor :: (HasProgramEnv m, MonadError TypeError m) => DataCtor -> m DataCtorType
findDataCtor k = lookupDataCtor k `orThrowM` UnboundDataCtor k

findTermVar :: (HasTypeEnv m, MonadError TypeError m) => TermVar -> m TypeScheme
findTermVar x = lookupTermVar x `orThrowM` UnboundTermVar x

class Instantiable f where
  instantiate :: Applicative m => (TypeVar -> m (Monotype UniVar)) -> f Void -> m (f UniVar)

instance Instantiable Monotype where
  instantiate f (VarType v) = f v
  instantiate f (ApplyType k ts) = ApplyType k <$> traverse (instantiate f) ts
  instantiate f (FamilyApplyType k ts) = FamilyApplyType k <$> traverse (instantiate f) ts

instance Instantiable Constraint where
  instantiate _ EmptyConstraint = pure EmptyConstraint
  instantiate f (ProductConstraint q1 q2) = ProductConstraint <$> instantiate f q1 <*> instantiate f q2
  instantiate f (EqualityConstraint t1 t2) = EqualityConstraint <$> instantiate f t1 <*> instantiate f t2
  instantiate f (TypeClassConstraint k ts) = TypeClassConstraint k <$> traverse (instantiate f) ts
