{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}

module Language.Simple.Type.Generator (generateConstraint) where

import Control.Monad (unless, when)
import Control.Monad.Except (MonadError (..))
import Data.Foldable (foldlM)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (empty, insert, intersection, keys, lookup, member, union)
import qualified Data.HashSet as HashSet (delete, difference, union)
import qualified Data.Vector as Vector (length, zip)
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
    upgradeConstraint,
    upgradeMonotype,
  )
import Language.Simple.Type.Constraint (GeneratedConstraint (..), UniVar, fuv)
import Language.Simple.Type.Env (HasLocalTypeEnv (..), HasProgramEnv (..), HasTypeEnv (..))
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Util (foldMapM, orThrow, orThrowM)

generateConstraint ::
  ( HasLocalTypeEnv m,
    HasTypeEnv m,
    HasProgramEnv m,
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
      universalSubst <- fromBinders @UniVar universalVars
      existentialSubst <- fromBinders @TypeVar existentialVars
      subst <- compose (upgradeTypeVarSubst universalSubst) (upgradeTypeVarSubst existentialSubst)
      constraint' <- instantiateConstraint subst constraint
      fields' <- mapM (instantiateMonotype subst) fields
      ctorArgs' <- mapM (instantiateMonotype subst . VarType) ctorArgs
      -- generate constraints from arm body
      unless (Vector.length vars == Vector.length fields) $
        throwError MismatchedNumberOfDataCtorFields {ctor = k, expected = Vector.length fields, got = Vector.length vars}
      (tBody, cBody) <- withLocalVars vars fields' $ generateConstraint body
      -- calculate \( \delta \)
      envFuv <- localEnvFuv
      let delta' = (fuv tBody `HashSet.union` fuv cBody) `HashSet.difference` envFuv
      let delta = foldr HashSet.delete delta' (unTypeVarSubst universalSubst)
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
      let c = c1 <> Constraint (EqualityConstraint t1 (upgradeMonotype monotype))
      pure (t2, c1 <> c2 <> ExistentialGeneratedConstraint delta (upgradeConstraint constraint) c)

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
  subst <- fromBinders @UniVar vars
  q <- instantiateConstraint subst constraint
  t <- instantiateMonotype subst monotype
  pure (t, q)

newtype TypeVarSubst a = TypeVarSubst {unTypeVarSubst :: HashMap TypeVar a}

class SubstTo a where
  toMonotype :: a -> Monotype UniVar

instance SubstTo UniVar where
  toMonotype = UniType

instance SubstTo TypeVar where
  toMonotype = VarType

instance SubstTo (Monotype UniVar) where
  toMonotype = id

upgradeTypeVarSubst :: SubstTo a => TypeVarSubst a -> TypeVarSubst (Monotype UniVar)
upgradeTypeVarSubst (TypeVarSubst m) = TypeVarSubst $ fmap toMonotype m

fromBinders ::
  forall a m t.
  ( Foldable t,
    Fresh m,
    GenFresh a,
    MonadError TypeError m
  ) =>
  t TypeVar ->
  m (TypeVarSubst a)
fromBinders binders = TypeVarSubst <$> foldlM f HashMap.empty binders
  where
    f acc v = do
      when (HashMap.member v acc) $ throwError (ConflictingTypeVars v)
      a <- fresh
      pure $ HashMap.insert v a acc

compose :: MonadError TypeError m => TypeVarSubst a -> TypeVarSubst a -> m (TypeVarSubst a)
compose (TypeVarSubst m1) (TypeVarSubst m2)
  | null intersection = pure . TypeVarSubst $ HashMap.union m1 m2
  | otherwise = throwError . ConflictingTypeVars . head $ HashMap.keys intersection
  where
    intersection = HashMap.intersection m1 m2

instantiateMonotype :: (SubstTo a, MonadError TypeError m) => TypeVarSubst a -> SimpleMonotype -> m (Monotype UniVar)
instantiateMonotype (TypeVarSubst m) (VarType v) = toMonotype <$> HashMap.lookup v m `orThrow` UnboundTypeVar v
instantiateMonotype s (ApplyType k ts) = ApplyType k <$> mapM (instantiateMonotype s) ts

instantiateConstraint :: (SubstTo a, MonadError TypeError m) => TypeVarSubst a -> SimpleConstraint -> m (Constraint UniVar)
instantiateConstraint _ EmptyConstraint = pure EmptyConstraint
instantiateConstraint s (ProductConstraint c1 c2) = ProductConstraint <$> instantiateConstraint s c1 <*> instantiateConstraint s c2
instantiateConstraint s (EqualityConstraint t1 t2) = EqualityConstraint <$> instantiateMonotype s t1 <*> instantiateMonotype s t2

findDataCtor :: (HasProgramEnv m, MonadError TypeError m) => DataCtor -> m DataCtorType
findDataCtor k = lookupDataCtor k `orThrowM` UnboundDataCtor k

findTermVar :: (HasTypeEnv m, MonadError TypeError m) => TermVar -> m TypeScheme
findTermVar x = lookupTermVar x `orThrowM` UnboundTermVar x
