{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Core.Type (checkProgram) where

import Control.Monad (forM_, unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Data.Foldable (traverse_)
import Data.Functor (void, ($>))
import Data.Hashable (Hashable)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (length, zip, (!?))
import Language.Core.Syntax
  ( AxiomName,
    AxiomScheme (..),
    Binding (..),
    CaseArm (..),
    Coercion (..),
    CoercionVar,
    CoercionVarBinder (..),
    CompleteCoercion,
    CompleteCoercionVarBinder,
    CompleteExpr,
    CompleteProposition,
    CompleteTermVarBinder,
    CompleteType,
    DataCtor,
    DataCtorType (..),
    Expr (..),
    Program (..),
    Proposition (..),
    TermVar,
    TermVarBinder (..),
    Type (..),
    TypeCtor,
    TypeVar,
    takePropositionLhs,
    takePropositionRhs,
    pattern FunctionType,
  )
import Language.Core.Type.Env
  ( EnvT,
    lookupAxiomScheme,
    lookupCoercionVar,
    lookupDataCtor,
    lookupTermVar,
    lookupTypeVar,
    runEmptyEnvT,
    runEnvT,
    withCoercionVar,
    withTermVar,
    withTypeVar,
  )
import Language.Core.Type.Error (TypeError (..))
import Language.Core.Type.Substitution (substProposition, substType)
import qualified Language.Core.Type.Substitution as Subst (fromVars, singleton)
import Language.Simple.Fresh (Fresh (..))
import Prettyprinter (pretty, (<+>))
import Util (findDuplicate, logDocInfo, orThrowM)

checkProgram :: (MonadLogger m, MonadError TypeError m) => Program -> m ()
checkProgram Program {bindings, axioms, vars, dataCtors} = do
  traverse_ checkAxiom axioms
  runEmptyEnvT $ traverse_ checkType vars
  traverse_ checkDataCtor dataCtors
  runEnvT axioms vars dataCtors $ foldr go (pure ()) bindings
  where
    go binding@(Binding b _) acc = do
      logDocInfo $ "checking" <+> pretty b
      checkBinding binding >> withTermVar b acc

checkAxiom :: (MonadLogger m, MonadError TypeError m) => AxiomScheme -> m ()
checkAxiom ForallAxiomScheme {vars, lhs, rhs} = do
  assertDistinctTypeVar vars
  runEmptyEnvT $
    withTypeVars vars $ do
      checkType lhs
      checkType rhs

checkDataCtor :: (MonadLogger m, MonadError TypeError m) => DataCtorType -> m ()
checkDataCtor DataCtorType {universalVars, existentialVars, fields, ctor, ctorArgs} = do
  assertDistinctTypeVar (universalVars <> existentialVars)
  runEmptyEnvT $
    withTypeVars universalVars $
      withTypeVars existentialVars $ do
        traverse_ checkType fields
        checkType (ApplyType ctor $ fmap VarType ctorArgs)

checkBinding :: (MonadLogger m, MonadError TypeError m) => Binding -> EnvT m ()
checkBinding (Binding b e) = void . withTermVar b $ typeExpr e

typeExpr :: (MonadLogger m, MonadError TypeError m) => CompleteExpr -> EnvT m CompleteType
typeExpr (CtorExpr k) = do
  DataCtorType
    { universalVars,
      existentialVars,
      coercionVars,
      fields,
      ctor,
      ctorArgs
    } <-
    findDataCtor k
  let funTy = foldr FunctionType (ApplyType ctor $ fmap VarType ctorArgs) fields
  refreshType $ foldr ForallType (foldr ForallType (foldr CoercionForallType funTy coercionVars) existentialVars) universalVars
typeExpr (VarExpr x) = refreshType =<< findTermVar x
typeExpr (LambdaExpr b@(TermVarBinder _ paramTy) e) = do
  checkType paramTy
  bodyTy <- withTermVar b $ typeExpr e
  pure $ FunctionType paramTy bodyTy
typeExpr (TypeLambdaExpr v e) = do
  bodyTy <- withTypeVar v $ typeExpr e
  pure $ ForallType v bodyTy
typeExpr (CoercionLambdaExpr b@(CoercionVarBinder _ p) e) = do
  bodyTy <- withCoercionVar b $ typeExpr e
  pure $ CoercionForallType p bodyTy
typeExpr (ApplyExpr e1 e2) = do
  t1 <- typeExpr e1
  (paramTy, bodyTy) <- assertFunctionType t1
  t2 <- typeExpr e2
  assertTypeMatch t2 paramTy
  pure bodyTy
typeExpr (TypeApplyExpr e t) = do
  checkType t
  lhs <- typeExpr e
  (v, bodyTy) <- assertForallType lhs
  pure $ substType (Subst.singleton v t) bodyTy
typeExpr (CoercionApplyExpr e c) = do
  t <- typeExpr e
  p <- coercionProposition c
  (p', bodyTy) <- assertCoercionForallType t
  assertPropositionMatch p p'
  pure bodyTy
typeExpr (CaseExpr e armTy arms) = do
  t <- typeExpr e
  (k, params) <- assertApplyType t
  forM_ arms $ \arm -> do
    armTy' <- typeArm k params arm
    assertTypeMatch armTy' armTy
  pure armTy
  where
    typeArm k params CaseArm {ctor, typeArgs, existentialVars, coercionVars, termVars, body} = do
      DataCtorType
        { universalVars,
          existentialVars = existentialVars',
          coercionVars = coercionVars',
          fields,
          ctor = k',
          ctorArgs
        } <-
        findDataCtor ctor
      assertLengthMatch universalVars typeArgs
      traverse_ checkType typeArgs
      assertLengthMatch existentialVars existentialVars'
      let subst = Subst.fromVars (universalVars <> existentialVars') (typeArgs <> fmap VarType existentialVars)
      assertLengthMatch coercionVars coercionVars'
      forM_ (Vector.zip coercionVars coercionVars') $
        \(CoercionVarBinder _ p, p') -> assertPropositionMatch p (substProposition subst p')
      withTypeVars existentialVars $
        withCoercionVars coercionVars $ do
          assertLengthMatch termVars fields
          forM_ (Vector.zip termVars fields) $
            \(TermVarBinder _ t, t') -> do
              checkType t
              assertTypeMatch t (substType subst t')
          assertTypeCtorMatch k k'
          assertLengthMatch params ctorArgs
          forM_ (Vector.zip params ctorArgs) $
            \(t, t') -> assertTypeMatch t (substType subst (VarType t'))
          withTermVars termVars $ typeExpr body
typeExpr (LetExpr _ b@(TermVarBinder _ t) e1 e2) = do
  checkType t
  t1 <- withTermVar b $ typeExpr e1
  assertTypeMatch t1 t
  withTermVar b $ typeExpr e2
typeExpr (CastExpr e c) = do
  t <- typeExpr e
  Proposition t1 t2 <- coercionProposition c
  assertTypeMatch t t1
  pure t2

refreshType :: Fresh m => CompleteType -> m CompleteType
refreshType (ForallType v t) = do
  v' <- fresh
  t' <- refreshType (substType (Subst.singleton v (VarType v')) t)
  pure (ForallType v' t')
refreshType t = pure t

coercionProposition :: MonadError TypeError m => CompleteCoercion -> EnvT m CompleteProposition
coercionProposition (AxiomCoercion n tys) = do
  ForallAxiomScheme {vars, lhs, rhs} <- findAxiomScheme n
  assertLengthMatch vars tys
  let subst = Subst.fromVars vars tys
  pure $ Proposition (substType subst lhs) (substType subst rhs)
coercionProposition (VarCoercion v) = findCoercionVar v
coercionProposition (TypeCtorCoercion k cs) = do
  ps <- traverse coercionProposition cs
  let lhs = ApplyType k (fmap takePropositionLhs ps)
  let rhs = ApplyType k (fmap takePropositionRhs ps)
  pure $ Proposition lhs rhs
coercionProposition (FamilyCoercion k cs) = do
  ps <- traverse coercionProposition cs
  let lhs = FamilyApplyType k (fmap takePropositionLhs ps)
  let rhs = FamilyApplyType k (fmap takePropositionRhs ps)
  pure $ Proposition lhs rhs
coercionProposition (RightCoercion n c) = do
  Proposition lhs rhs <- coercionProposition c
  (_, ts1) <- assertApplyType lhs
  (_, ts2) <- assertApplyType rhs
  t1 <- assertIndex ts1 n
  t2 <- assertIndex ts2 n
  pure (Proposition t1 t2)
coercionProposition (ReflCoercion t) = checkType t $> Proposition t t
coercionProposition (TransCoercion c1 c2) = do
  Proposition lhs1 rhs1 <- coercionProposition c1
  Proposition lhs2 rhs2 <- coercionProposition c2
  assertTypeMatch rhs1 lhs2
  pure $ Proposition lhs1 rhs2
coercionProposition (SymmCoercion c) = do
  Proposition t1 t2 <- coercionProposition c
  pure $ Proposition t2 t1
coercionProposition (EquivalentCoercion c1 c2) = do
  p1 <- coercionProposition c1
  p2 <- coercionProposition c2
  assertPropositionMatch p1 p2
  pure p1

checkType :: MonadError TypeError m => CompleteType -> EnvT m ()
checkType (VarType v) = findTypeVar v
checkType (ApplyType _ ts) = traverse_ checkType ts
checkType (FamilyApplyType _ ts) = traverse_ checkType ts
checkType (ForallType v t) = withTypeVar v $ checkType t
checkType (CoercionForallType _ t) = checkType t

assertIndex :: MonadError TypeError m => Vector CompleteType -> Int -> m CompleteType
assertIndex ts n = case ts Vector.!? n of
  Just t -> pure t
  Nothing -> throwError $ InvalidIndex ts n

assertTypeMatch :: MonadError TypeError m => CompleteType -> CompleteType -> m ()
assertTypeMatch = assertEq TypeMismatch

assertDistinctTypeVar :: MonadError TypeError m => Vector TypeVar -> m ()
assertDistinctTypeVar = assertDistinct DuplicateTypeVar

assertLengthMatch :: MonadError TypeError m => Vector a -> Vector b -> m ()
assertLengthMatch (Vector.length -> l1) (Vector.length -> l2)
  | l1 == l2 = pure ()
  | otherwise = throwError $ LengthMismatch l1 l2

assertTypeCtorMatch :: MonadError TypeError m => TypeCtor -> TypeCtor -> m ()
assertTypeCtorMatch = assertEq TypeCtorMismatch

assertPropositionMatch :: MonadError TypeError m => CompleteProposition -> CompleteProposition -> m ()
assertPropositionMatch = assertEq PropositionMismatch

assertDistinct :: (Eq a, Hashable a, MonadError TypeError m) => (a -> TypeError) -> Vector a -> m ()
assertDistinct f v
  | Just x <- findDuplicate v = throwError $ f x
  | otherwise = pure ()

assertEq :: (Eq a, MonadError TypeError m) => (a -> a -> TypeError) -> a -> a -> m ()
assertEq p x1 x2
  | x1 == x2 = pure ()
  | otherwise = throwError (p x1 x2)

assertApplyType :: MonadError TypeError m => CompleteType -> m (TypeCtor, Vector CompleteType)
assertApplyType (ApplyType k ts) = pure (k, ts)
assertApplyType t = throwError $ ApplyTypeExpected t

assertCoercionForallType :: MonadError TypeError m => CompleteType -> m (CompleteProposition, CompleteType)
assertCoercionForallType (CoercionForallType p t) = pure (p, t)
assertCoercionForallType t = throwError $ CoercionForallTypeExpected t

assertForallType :: MonadError TypeError m => CompleteType -> m (TypeVar, CompleteType)
assertForallType (ForallType v t) = pure (v, t)
assertForallType t = throwError $ ForallTypeExpected t

assertFunctionType :: MonadError TypeError m => CompleteType -> m (CompleteType, CompleteType)
assertFunctionType (FunctionType t1 t2) = pure (t1, t2)
assertFunctionType t = throwError $ FunctionTypeExpected t

withTermVars :: (Monad m, Foldable f) => f CompleteTermVarBinder -> EnvT m a -> EnvT m a
withTermVars t a = foldr withTermVar a t

withCoercionVars :: (Monad m, Foldable f) => f CompleteCoercionVarBinder -> EnvT m a -> EnvT m a
withCoercionVars t a = foldr withCoercionVar a t

withTypeVars :: (Monad m, Foldable f) => f TypeVar -> EnvT m a -> EnvT m a
withTypeVars t a = foldr withTypeVar a t

findDataCtor :: MonadError TypeError m => DataCtor -> EnvT m DataCtorType
findDataCtor k = lookupDataCtor k `orThrowM` UnboundDataCtor k

findTermVar :: MonadError TypeError m => TermVar -> EnvT m CompleteType
findTermVar x = lookupTermVar x `orThrowM` UnboundTermVar x

findTypeVar :: MonadError TypeError m => TypeVar -> EnvT m ()
findTypeVar x = do
  found <- lookupTypeVar x
  unless found $ throwError (UnboundTypeVar x)

findAxiomScheme :: MonadError TypeError m => AxiomName -> EnvT m AxiomScheme
findAxiomScheme x = lookupAxiomScheme x `orThrowM` UnboundAxiomName x

findCoercionVar :: MonadError TypeError m => CoercionVar -> EnvT m CompleteProposition
findCoercionVar x = lookupCoercionVar x `orThrowM` UnboundCoercionVar x
