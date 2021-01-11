{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Simple.Type.Generator
  ( generateConstraint,
    toCoreType,
    toCoreTypeCtor,
    applyConstraints,
    atomicConstraints,
    applyGivenToExpr,
    applyGivenToType,
    applyGivenTypesToType,
    toCompleteCoreType,
    newEquality,
    applyTypeScheme,
  )
where

import Control.Monad (unless, when)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Writer.CPS (execWriterT, runWriterT, tell)
import Data.Foldable (foldl', foldlM)
import qualified Data.HashMap.Strict as HashMap (insert, intersection, keys, member, union)
import qualified Data.HashSet as HashSet (delete, difference, union)
import qualified Data.Vector as Vector (fromList, length, zip, zipWith)
import Data.Void (Void, vacuous)
import qualified Language.Core.Syntax as Core
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
    TypeCtor (..),
    TypeScheme (..),
    TypeVar,
    functionType,
  )
import Language.Simple.Type.Constraint
  ( AtomicConstraint (..),
    Fuv (..),
    GeneratedConstraint (..),
    GeneratedCoreCoercion,
    GeneratedCoreCoercionVarBinder,
    GeneratedCoreExpr,
    GeneratedCoreTermVarBinder,
    GeneratedCoreType,
    GivenConstraint (..),
    UniVar,
  )
import Language.Simple.Type.Env (HasLocalTypeEnv (..), HasProgramEnv (..), HasTypeEnv (..))
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Instantiator, Subst (..))
import qualified Language.Simple.Type.Substitution as Subst (replaceAll)
import Util (orThrowM)

generateConstraint ::
  ( HasLocalTypeEnv m,
    HasTypeEnv m,
    HasProgramEnv m,
    MonadLogger m,
    Fresh m,
    MonadError TypeError m
  ) =>
  Expr ->
  m (GeneratedCoreExpr, Monotype UniVar, GeneratedConstraint)
generateConstraint (CtorExpr k) = do
  s <- dataCtorTypeToTypeScheme <$> findDataCtor k
  (e, t, qs) <- instantiateTypeScheme (Core.CtorExpr k) s
  pure (e, t, foldMap AtomicGeneratedConstraint qs)
generateConstraint (VarExpr x) =
  lookupLocalVar x >>= \case
    Just t -> pure (Core.VarExpr x, t, EmptyGeneratedConstraint)
    Nothing -> do
      s <- findTermVar x
      (e, t, qs) <- instantiateTypeScheme (Core.VarExpr x) s
      pure (e, t, foldMap AtomicGeneratedConstraint qs)
generateConstraint (LambdaExpr x e) = do
  u <- fresh
  (e', t, c) <- withLocalVar x (UniType u) $ generateConstraint e
  let lambdaExpr = Core.LambdaExpr (Core.TermVarBinder x (Core.UniType u)) e'
  pure (lambdaExpr, functionType (UniType u) t, c)
generateConstraint (ApplyExpr e1 e2) = do
  (e1', t1, c1) <- generateConstraint e1
  (e2', t2, c2) <- generateConstraint e2
  u <- fresh
  (lhsCo, lhsQ) <- newEquality t1 (functionType t2 (UniType u))
  let applyExpr = Core.ApplyExpr (Core.CastExpr e1' lhsCo) e2'
  pure (applyExpr, UniType u, c1 <> c2 <> AtomicGeneratedConstraint lhsQ)
generateConstraint (CaseExpr e arms) = do
  (e', t, c) <- generateConstraint e
  ret <- fresh
  (arms', (scrutineeCoercions, cArms)) <- runWriterT $ mapM (generateForArm t (UniType ret)) arms
  let scrutinee = case scrutineeCoercions of
        [] -> e'
        [c'] -> Core.CastExpr e' c'
        cs -> Core.CastExpr e' (foldr1 Core.EquivalentCoercion cs)
  let caseExpr = Core.CaseExpr scrutinee (Core.UniType ret) arms'
  pure (caseExpr, UniType ret, c <> cArms)
  where
    withLocalVars xs ts m = foldr (uncurry withLocalVar) m $ Vector.zip xs ts
    isGADT exs EmptyConstraint | null exs = False
    isGADT _ _ = True
    generateForArm tScrutinee tCase arm = do
      (scrutineeCo, cOut, caseArm) <- lift $ generateForArm' tScrutinee tCase arm
      tell (scrutineeCo, cOut)
      pure caseArm
    generateForArm' tScrutinee tCase CaseArm {ctor = k, vars, body} = do
      DataCtorType {universalVars, existentialVars, constraint, fields, ctor, ctorArgs} <- findDataCtor k
      -- instantiate data constructor type
      (universalSubst, universalUniVars) <- fromBinders UniType universalVars
      (existentialSubst, existentialTypeVars) <- fromBinders VarType existentialVars
      subst <- composeInstantiator universalSubst existentialSubst
      constraint' <- instantiateConstraint subst constraint
      fields' <- mapM (instantiateMonotype subst) fields
      ctorArgs' <- mapM (instantiateMonotype subst . VarType) ctorArgs
      (coercionVars, dictFields, constraint') <- givenConstraints constraint'
      -- generate constraints from arm body
      unless (Vector.length vars == Vector.length fields) $
        throwError MismatchedNumberOfDataCtorFields {ctor = k, expected = Vector.length fields, got = Vector.length vars}
      (body', tBody, cBody) <- withLocalVars vars fields' $ generateConstraint body
      -- calculate \( \delta \)
      envFuv <- localEnvFuv
      let delta' = (fuv tBody <> fuv cBody) `HashSet.difference` envFuv
      let delta = foldr HashSet.delete delta' universalUniVars
      -- produce final constraint \( C'_i \)
      (bodyCo, bodyQ) <- newEquality tBody tCase
      let cArm = cBody <> AtomicGeneratedConstraint bodyQ
      (scrutineeCo, scrutineeQ) <- newEquality tScrutinee (ApplyType ctor ctorArgs')
      let cScrutinee = AtomicGeneratedConstraint scrutineeQ
      (implicationId, cOut) <-
        if isGADT existentialVars constraint
          then do
            iid <- fresh
            pure (Just iid, ExistentialGeneratedConstraint iid delta constraint' cArm <> cScrutinee)
          else pure (Nothing, cArm <> cScrutinee)
      let caseArm =
            Core.CaseArm
              { implicationId,
                ctor = k,
                typeArgs = Vector.fromList (map Core.UniType universalUniVars),
                existentialVars = Vector.fromList existentialTypeVars,
                coercionVars = Vector.fromList coercionVars,
                termVars = Vector.fromList dictFields <> Vector.zipWith Core.TermVarBinder vars (fmap toCoreType fields'),
                body = Core.CastExpr body' bodyCo
              }
      pure ([scrutineeCo], cOut, caseArm)
generateConstraint (UnannotatedLetExpr x e1 e2) = do
  (e1', t1, c1) <- generateConstraint e1
  (e2', t2, c2) <- withLocalVar x t1 $ generateConstraint e2
  let letExpr = Core.LetExpr Nothing (Core.TermVarBinder x (toCoreType t1)) e1' e2'
  pure (letExpr, t2, c1 <> c2)
generateConstraint (AnnotatedLetExpr x s e1 e2)
  | isMono s = generateForMono
  | otherwise = generateForPoly
  where
    isMono ForallTypeScheme {vars, constraint = EmptyConstraint} | null vars = True
    isMono _ = False
    generateForMono = do
      (e1', t1, c1) <- generateConstraint e1
      (e2', t2, c2) <- withTermVar x s $ generateConstraint e2
      let ForallTypeScheme {monotype} = s
      (lhsCo, lhsQ) <- newEquality t1 (vacuous monotype)
      let letExpr = Core.LetExpr Nothing (Core.TermVarBinder x (toCoreType (vacuous monotype))) (Core.CastExpr e1' lhsCo) e2'
      pure (letExpr, t2, c1 <> c2 <> AtomicGeneratedConstraint lhsQ)
    generateForPoly = do
      (e1', t1, c1) <- generateConstraint e1
      (e2', t2, c2) <- withTermVar x s $ generateConstraint e2
      let ForallTypeScheme {monotype} = s
      envFuv <- localEnvFuv
      let delta = (fuv t1 `HashSet.union` fuv c1) `HashSet.difference` envFuv
      (lhsCo, lhsQ) <- newEquality t1 (vacuous monotype)
      (given, s', wrapped) <- applyTypeScheme s (Core.CastExpr e1' lhsCo)
      implicationId <- fresh
      let letExpr = Core.LetExpr (Just implicationId) (Core.TermVarBinder x s') wrapped e2'
      let c = c1 <> AtomicGeneratedConstraint lhsQ
      pure (letExpr, t2, c2 <> ExistentialGeneratedConstraint implicationId delta given c)

applyTypeScheme :: Fresh m => TypeScheme -> GeneratedCoreExpr -> m ([GivenConstraint], GeneratedCoreType, GeneratedCoreExpr)
applyTypeScheme ForallTypeScheme {vars, constraint, monotype} e = do
  (coercionVars, dictFields, given) <- givenConstraints (vacuous constraint)
  let t' = applyGivenToType vars coercionVars dictFields (toCoreType (vacuous monotype))
  let e' = applyGivenToExpr vars coercionVars dictFields e
  pure (given, t', e')

applyGivenToExpr ::
  Foldable f =>
  f TypeVar ->
  [GeneratedCoreCoercionVarBinder] ->
  [GeneratedCoreTermVarBinder] ->
  GeneratedCoreExpr ->
  GeneratedCoreExpr
applyGivenToExpr vars coercionVars dictFields e =
  foldr Core.TypeLambdaExpr (foldr Core.CoercionLambdaExpr (foldr Core.LambdaExpr e dictFields) coercionVars) vars

applyGivenToType ::
  Foldable f =>
  f TypeVar ->
  [GeneratedCoreCoercionVarBinder] ->
  [GeneratedCoreTermVarBinder] ->
  GeneratedCoreType ->
  GeneratedCoreType
applyGivenToType vars coercionVars dictFields = applyGivenTypesToType vars (map takeProposition coercionVars) (map takeType dictFields)
  where
    takeType (Core.TermVarBinder _ t') = t'
    takeProposition (Core.CoercionVarBinder _ p) = p

applyGivenTypesToType ::
  Foldable f =>
  f TypeVar ->
  [Core.Proposition a] ->
  [Core.Type a] ->
  Core.Type a ->
  Core.Type a
applyGivenTypesToType vars ps ts t =
  foldr Core.ForallType (foldr Core.CoercionForallType (foldr Core.FunctionType t ts) ps) vars

toCoreType :: Monotype UniVar -> GeneratedCoreType
toCoreType (VarType v) = Core.VarType v
toCoreType (UniType u) = Core.UniType u
toCoreType (ApplyType k ts) = Core.ApplyType (toCoreTypeCtor k) (fmap toCoreType ts)
toCoreType (FamilyApplyType k ts) = Core.FamilyApplyType k (fmap toCoreType ts)

toCompleteCoreType :: SimpleMonotype -> Core.CompleteType
toCompleteCoreType (VarType v) = Core.VarType v
toCompleteCoreType (ApplyType k ts) = Core.ApplyType (toCoreTypeCtor k) (fmap toCompleteCoreType ts)
toCompleteCoreType (FamilyApplyType k ts) = Core.FamilyApplyType k (fmap toCompleteCoreType ts)

toCoreTypeCtor :: TypeCtor -> Core.TypeCtor
toCoreTypeCtor (NamedTypeCtor k) = Core.NamedTypeCtor k
toCoreTypeCtor FunctionTypeCtor = Core.FunctionTypeCtor

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
  GeneratedCoreExpr ->
  TypeScheme ->
  m (GeneratedCoreExpr, Monotype UniVar, [AtomicConstraint])
instantiateTypeScheme e ForallTypeScheme {vars, constraint, monotype} = do
  (subst, uniVars) <- fromBinders UniType vars
  let e' = foldl' (\acc -> Core.TypeApplyExpr acc . Core.UniType) e uniVars
  q <- instantiateConstraint subst constraint
  qs <- atomicConstraints q
  t <- instantiateMonotype subst monotype
  pure (applyConstraints qs e', t, qs)

applyConstraints :: [AtomicConstraint] -> GeneratedCoreExpr -> GeneratedCoreExpr
applyConstraints qs = applyDictionaryConstraints qs . applyEqualityConstraints qs

applyEqualityConstraints :: [AtomicConstraint] -> GeneratedCoreExpr -> GeneratedCoreExpr
applyEqualityConstraints qs e = foldl' go e qs
  where
    go acc (EqualityAtomicConstraint id _ _) = Core.CoercionApplyExpr acc (Core.UnsolvedCoercion id)
    go acc TypeClassAtomicConstraint {} = acc

applyDictionaryConstraints :: [AtomicConstraint] -> GeneratedCoreExpr -> GeneratedCoreExpr
applyDictionaryConstraints qs e = foldl' go e qs
  where
    go acc (TypeClassAtomicConstraint id _ _) = Core.ApplyExpr acc (Core.UnsolvedClassDictionaryExpr id)
    go acc EqualityAtomicConstraint {} = acc

atomicConstraints :: Fresh m => Constraint UniVar -> m [AtomicConstraint]
atomicConstraints EmptyConstraint = pure mempty
atomicConstraints (ProductConstraint q1 q2) = do
  qs1 <- atomicConstraints q1
  qs2 <- atomicConstraints q2
  pure (qs1 <> qs2)
atomicConstraints (EqualityConstraint t1 t2) = do
  id <- fresh
  pure [EqualityAtomicConstraint id t1 t2]
atomicConstraints (TypeClassConstraint k ts) = do
  id <- fresh
  pure [TypeClassAtomicConstraint id k ts]

givenConstraints :: Fresh m => Constraint UniVar -> m ([GeneratedCoreCoercionVarBinder], [GeneratedCoreTermVarBinder], [GivenConstraint])
givenConstraints = execWriterT . go
  where
    go EmptyConstraint = pure ()
    go (ProductConstraint q1 q2) = go q1 >> go q2
    go (EqualityConstraint t1 t2) = do
      c <- fresh
      let binder = Core.CoercionVarBinder c (Core.Proposition (toCoreType t1) (toCoreType t2))
      let q = EqualityGivenConstraint (Core.VarCoercion c) t1 t2
      tell ([binder], [], [q])
    go (TypeClassConstraint k ts) = do
      v <- fresh
      let binder = Core.TermVarBinder v (Core.ApplyType (Core.ClassDictionaryTypeCtor k) (fmap toCoreType ts))
      let q = TypeClassGivenConstraint (Core.VarExpr v) k ts
      tell ([], [binder], [q])

newEquality :: Fresh m => Monotype UniVar -> Monotype UniVar -> m (GeneratedCoreCoercion, AtomicConstraint)
newEquality t1 t2 = do
  id <- fresh
  pure (Core.UnsolvedCoercion id, EqualityAtomicConstraint id t1 t2)

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
      pure (HashMap.insert v (toMonotype a) subst, vars ++ [a])
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
