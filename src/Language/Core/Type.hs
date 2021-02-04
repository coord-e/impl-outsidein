{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Core.Type (checkProgram) where

import Control.Monad (forM, forM_, unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Data.Foldable (traverse_)
import Data.Functor (($>))
import Data.Hashable (Hashable)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, length, unzip, zip, (!), (!?))
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
import Prettyprinter (pretty, (<+>))
import Util (findDuplicate, logDocInfo, orThrowM)

checkProgram :: (MonadLogger m, MonadError TypeError m) => Program -> m Program
checkProgram p@Program {bindings, axioms, vars, dataCtors} = do
  traverse_ checkAxiom axioms
  runEmptyEnvT $ traverse_ checkType vars
  traverse_ checkDataCtor dataCtors
  bindings' <- runEnvT axioms vars dataCtors $ foldr go (pure []) bindings
  pure p {bindings = Vector.fromList bindings'}
  where
    go binding@(Binding b _) acc = do
      logDocInfo $ "checking" <+> pretty b
      binding' <- checkBinding binding
      acc' <- withTermVar b acc
      pure (binding' : acc')

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

checkBinding :: (MonadLogger m, MonadError TypeError m) => Binding -> EnvT m Binding
checkBinding (Binding b e) = do
  (e', _) <- withTermVar b $ typeExpr e
  pure (Binding b e')

typeExpr :: (MonadLogger m, MonadError TypeError m) => CompleteExpr -> EnvT m (CompleteExpr, CompleteType)
typeExpr e@(CtorExpr k) = do
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
  let t = foldr ForallType (foldr ForallType (foldr CoercionForallType funTy coercionVars) existentialVars) universalVars
  pure (e, t)
typeExpr e@(VarExpr x) = do
  t <- findTermVar x
  pure (e, t)
typeExpr (LambdaExpr b@(TermVarBinder _ paramTy) e) = do
  checkType paramTy
  (e', bodyTy) <- withTermVar b $ typeExpr e
  pure (LambdaExpr b e', FunctionType paramTy bodyTy)
typeExpr (TypeLambdaExpr v e) = do
  (e', bodyTy) <- withTypeVar v $ typeExpr e
  pure (TypeLambdaExpr v e', ForallType v bodyTy)
typeExpr (CoercionLambdaExpr b@(CoercionVarBinder _ p) e) = do
  (e', bodyTy) <- withCoercionVar b $ typeExpr e
  pure (CoercionLambdaExpr b e', CoercionForallType p bodyTy)
typeExpr (ApplyExpr e1 e2) = do
  (e1', t1) <- typeExpr e1
  (paramTy, bodyTy) <- assertFunctionType t1
  (e2', t2) <- typeExpr e2
  assertTypeMatch t2 paramTy
  pure (ApplyExpr e1' e2', bodyTy)
typeExpr (TypeApplyExpr e t) = do
  checkType t
  (e', lhs) <- typeExpr e
  (v, bodyTy) <- assertForallType lhs
  bodyTy' <- substType (Subst.singleton v t) bodyTy
  pure (TypeApplyExpr e' t, bodyTy')
typeExpr (CoercionApplyExpr e c) = do
  (e', t) <- typeExpr e
  (c', p) <- coercionProposition c
  (p', bodyTy) <- assertCoercionForallType t
  assertPropositionMatch p p'
  pure (CoercionApplyExpr e' c', bodyTy)
typeExpr (CaseExpr e armTy arms) = do
  (e', t) <- typeExpr e
  (k, params) <- assertApplyType t
  arms' <- forM arms $ \arm -> do
    (arm', armTy') <- typeArm k params arm
    assertTypeMatch armTy' armTy
    pure arm'
  pure (CaseExpr e' armTy arms', armTy)
  where
    typeArm k params arm@CaseArm {ctor, typeArgs, existentialVars, coercionVars, termVars, body} = do
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
        \(CoercionVarBinder _ p, p') -> assertPropositionMatch p =<< substProposition subst p'
      withTypeVars existentialVars $
        withCoercionVars coercionVars $ do
          assertLengthMatch termVars fields
          forM_ (Vector.zip termVars fields) $
            \(TermVarBinder _ t, t') -> do
              checkType t
              assertTypeMatch t =<< substType subst t'
          assertTypeCtorMatch k k'
          assertLengthMatch params ctorArgs
          forM_ (Vector.zip params ctorArgs) $
            \(t, v) -> do
              t' <- substType subst (VarType v)
              assertTypeMatch t t'
          (body', bodyTy) <- withTermVars termVars $ typeExpr body
          pure (arm {body = body'}, bodyTy)
typeExpr (LetExpr mid b@(TermVarBinder _ t) e1 e2) = do
  checkType t
  (e1', t1) <- withTermVar b $ typeExpr e1
  assertTypeMatch t1 t
  (e2', t2) <- withTermVar b $ typeExpr e2
  pure (LetExpr mid b e1' e2', t2)
typeExpr (CastExpr e c) = do
  (e', t) <- typeExpr e
  (c', Proposition t1 t2) <- coercionProposition c
  assertTypeMatch t t1
  case c' of
    ReflCoercion _ -> pure (e', t2)
    _ -> pure (CastExpr e' c', t2)

coercionProposition :: MonadError TypeError m => CompleteCoercion -> EnvT m (CompleteCoercion, CompleteProposition)
coercionProposition c@(AxiomCoercion n tys) = do
  ForallAxiomScheme {vars, lhs, rhs} <- findAxiomScheme n
  assertLengthMatch vars tys
  let subst = Subst.fromVars vars tys
  lhs' <- substType subst lhs
  rhs' <- substType subst rhs
  pure (c, Proposition lhs' rhs')
coercionProposition c@(VarCoercion v) = do
  p <- findCoercionVar v
  pure (c, p)
coercionProposition (TypeCtorCoercion k cs) = do
  (cs', ps) <- Vector.unzip <$> traverse coercionProposition cs
  let lhs = ApplyType k (fmap takePropositionLhs ps)
  let rhs = ApplyType k (fmap takePropositionRhs ps)
  let proposition = Proposition lhs rhs
  case allRefl cs' of
    Just ts -> pure (ReflCoercion (ApplyType k ts), proposition)
    Nothing -> pure (TypeCtorCoercion k cs', proposition)
coercionProposition (FamilyCoercion k cs) = do
  (cs', ps) <- Vector.unzip <$> traverse coercionProposition cs
  let lhs = FamilyApplyType k (fmap takePropositionLhs ps)
  let rhs = FamilyApplyType k (fmap takePropositionRhs ps)
  let proposition = Proposition lhs rhs
  case allRefl cs' of
    Just ts -> pure (ReflCoercion (FamilyApplyType k ts), proposition)
    Nothing -> pure (FamilyCoercion k cs', proposition)
coercionProposition (RightCoercion n c) = do
  (c', Proposition lhs rhs) <- coercionProposition c
  (_, ts1) <- assertApplyType lhs
  (_, ts2) <- assertApplyType rhs
  t1 <- assertIndex ts1 n
  t2 <- assertIndex ts2 n
  let proposition = Proposition t1 t2
  case c' of
    ReflCoercion (ApplyType _ ts) -> pure (ReflCoercion (ts Vector.! n), proposition)
    _ -> pure (RightCoercion n c', proposition)
coercionProposition c@(ReflCoercion t) = checkType t $> (c, Proposition t t)
coercionProposition (TransCoercion c1 c2) = do
  (c1', Proposition lhs1 rhs1) <- coercionProposition c1
  (c2', Proposition lhs2 rhs2) <- coercionProposition c2
  assertTypeMatch rhs1 lhs2
  let proposition = Proposition lhs1 rhs2
  case (c1', c2') of
    (ReflCoercion _, _) -> pure (c2', proposition)
    (_, ReflCoercion _) -> pure (c1', proposition)
    (_, _) -> pure (TransCoercion c1' c2', proposition)
coercionProposition (SymmCoercion c) = do
  (c', Proposition t1 t2) <- coercionProposition c
  let proposition = Proposition t2 t1
  case c' of
    ReflCoercion _ -> pure (c', proposition)
    _ -> pure (SymmCoercion c', proposition)
coercionProposition (EquivalentCoercion c1 c2) = do
  (c1', p1) <- coercionProposition c1
  (_, p2) <- coercionProposition c2
  assertPropositionMatch p1 p2
  pure (c1', p1)

allRefl :: Vector CompleteCoercion -> Maybe (Vector CompleteType)
allRefl = traverse f
  where
    f (ReflCoercion t) = Just t
    f _ = Nothing

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
