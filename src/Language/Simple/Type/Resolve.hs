{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Simple.Type.Resolve
  ( resolveCore,
    resolveType,
  )
where

import Control.Monad.Reader (Reader, asks, local, runReader)
import qualified Data.HashMap.Strict as HashMap (lookup, union)
import Data.Text (pack)
import qualified Data.Vector as Vector (empty)
import qualified Language.Core.Syntax as Core
import Language.Simple.Type.Constraint
  ( DictionaryId,
    EqualityId,
    GeneratedCoreCaseArm,
    GeneratedCoreCoercion,
    GeneratedCoreCoercionVarBinder,
    GeneratedCoreExpr,
    GeneratedCoreProposition,
    GeneratedCoreTermVarBinder,
    GeneratedCoreType,
    UniVar,
  )
import Language.Simple.Type.Generator (toCoreType)
import Language.Simple.Type.Solver (ResultingUnifier (..))
import Language.Simple.Type.Solver.Evidence (EvidenceStore (..), emptyEvidenceStore)
import Language.Simple.Type.Substitution (Subst (..))
import qualified Language.Simple.Type.Substitution as Subst (lookup)

data ResolveEnv = ResolveEnv
  { evidences :: EvidenceStore,
    unifier :: ResultingUnifier
  }

newtype Resolve a = Resolve (Reader ResolveEnv a)
  deriving (Functor, Applicative, Monad)

runResolve :: Resolve a -> ResolveEnv -> a
runResolve (Resolve a) = runReader a

resolveDictionary :: DictionaryId -> Resolve GeneratedCoreExpr
resolveDictionary id = Resolve (asks $ f . evidences)
  where
    f EvidenceStore {dictionary} =
      case HashMap.lookup id dictionary of
        Just c -> c
        Nothing -> error $ "resolveDictionary: missing dictionary " <> show id

resolveEquality :: EqualityId -> Resolve GeneratedCoreCoercion
resolveEquality id = Resolve (asks $ f . evidences)
  where
    f EvidenceStore {equality} =
      case HashMap.lookup id equality of
        Just c -> c
        Nothing -> error $ "resolveEquality: missing equality " <> show id

withImplicationId :: Core.ImplicationId -> Resolve a -> Resolve a
withImplicationId id (Resolve a) = Resolve (local f a)
  where
    f e@ResolveEnv {unifier} = e {unifier = g unifier}
    g ResultingUnifier {simples, implications} =
      case HashMap.lookup id implications of
        Just ResultingUnifier {simples = innerSimples, implications = innerImplics} ->
          ResultingUnifier {simples = innerSimples `union` simples, implications = innerImplics}
        Nothing -> error $ "withImplicationId: missing implication id " <> show id
    union (Subst m1) (Subst m2) = Subst $ HashMap.union m1 m2

defaultType :: UniVar -> Core.CompleteType
defaultType u = Core.ApplyType (Core.NamedTypeCtor (pack $ "?" <> show u)) Vector.empty

fillCoreType :: GeneratedCoreType -> Core.CompleteType
fillCoreType (Core.UniType u) = defaultType u
fillCoreType (Core.VarType v) = Core.VarType v
fillCoreType (Core.ApplyType k ts) = Core.ApplyType k (fmap fillCoreType ts)
fillCoreType (Core.FamilyApplyType k ts) = Core.FamilyApplyType k (fmap fillCoreType ts)
fillCoreType (Core.ForallType v t) = Core.ForallType v (fillCoreType t)
fillCoreType (Core.CoercionForallType p t) = Core.CoercionForallType p' (fillCoreType t)
  where
    Core.Proposition t1 t2 = p
    p' = Core.Proposition (fillCoreType t1) (fillCoreType t2)

resolveUniVar :: UniVar -> Resolve Core.CompleteType
resolveUniVar u = Resolve (asks $ f . unifier)
  where
    f ResultingUnifier {simples} =
      case Subst.lookup u simples of
        Just t -> fillCoreType (toCoreType t)
        Nothing -> defaultType u

resolveCore :: EvidenceStore -> ResultingUnifier -> GeneratedCoreExpr -> Core.CompleteExpr
resolveCore evidences unifier e = runResolve (resolveCoreExpr e) env
  where
    env = ResolveEnv {evidences, unifier}

resolveType :: ResultingUnifier -> GeneratedCoreType -> Core.CompleteType
resolveType unifier t = runResolve (resolveCoreType t) env
  where
    env = ResolveEnv {evidences = emptyEvidenceStore, unifier}

resolveCoreExpr :: GeneratedCoreExpr -> Resolve Core.CompleteExpr
resolveCoreExpr (Core.UnsolvedClassDictionaryExpr id) = do
  e <- resolveDictionary id
  resolveCoreExpr e
resolveCoreExpr (Core.CtorExpr k) = pure (Core.CtorExpr k)
resolveCoreExpr (Core.VarExpr x) = pure (Core.VarExpr x)
resolveCoreExpr (Core.LambdaExpr b e) = do
  b' <- resolveCoreTermVarBinder b
  e' <- resolveCoreExpr e
  pure (Core.LambdaExpr b' e')
resolveCoreExpr (Core.TypeLambdaExpr v e) = do
  e' <- resolveCoreExpr e
  pure (Core.TypeLambdaExpr v e')
resolveCoreExpr (Core.CoercionLambdaExpr b e) = do
  b' <- resolveCoreCoercionVarBinder b
  e' <- resolveCoreExpr e
  pure (Core.CoercionLambdaExpr b' e')
resolveCoreExpr (Core.ApplyExpr e1 e2) = do
  e1' <- resolveCoreExpr e1
  e2' <- resolveCoreExpr e2
  pure (Core.ApplyExpr e1' e2')
resolveCoreExpr (Core.TypeApplyExpr e t) = do
  e' <- resolveCoreExpr e
  t' <- resolveCoreType t
  pure (Core.TypeApplyExpr e' t')
resolveCoreExpr (Core.CoercionApplyExpr e c) = do
  e' <- resolveCoreExpr e
  c' <- resolveCoreCoercion c
  pure (Core.CoercionApplyExpr e' c')
resolveCoreExpr (Core.CaseExpr e t arms) = do
  e' <- resolveCoreExpr e
  t' <- resolveCoreType t
  arms' <- traverse resolveCoreCaseArm arms
  pure (Core.CaseExpr e' t' arms')
resolveCoreExpr (Core.LetExpr mid b e1 e2) = do
  b' <- resolveCoreTermVarBinder b
  e1' <- case mid of
    Just id -> withImplicationId id (resolveCoreExpr e1)
    Nothing -> resolveCoreExpr e1
  e2' <- resolveCoreExpr e2
  pure (Core.LetExpr mid b' e1' e2')
resolveCoreExpr (Core.CastExpr e c) = do
  e' <- resolveCoreExpr e
  c' <- resolveCoreCoercion c
  pure (Core.CastExpr e' c')

resolveCoreTermVarBinder :: GeneratedCoreTermVarBinder -> Resolve Core.CompleteTermVarBinder
resolveCoreTermVarBinder (Core.TermVarBinder x t) = Core.TermVarBinder x <$> resolveCoreType t

resolveCoreCoercionVarBinder :: GeneratedCoreCoercionVarBinder -> Resolve Core.CompleteCoercionVarBinder
resolveCoreCoercionVarBinder (Core.CoercionVarBinder c p) = Core.CoercionVarBinder c <$> resolveCoreProposition p

resolveCoreProposition :: GeneratedCoreProposition -> Resolve Core.CompleteProposition
resolveCoreProposition (Core.Proposition t1 t2) = do
  t1' <- resolveCoreType t1
  t2' <- resolveCoreType t2
  pure (Core.Proposition t1' t2')

resolveCoreCaseArm :: GeneratedCoreCaseArm -> Resolve Core.CompleteCaseArm
resolveCoreCaseArm Core.CaseArm {Core.implicationId, Core.ctor, Core.typeArgs, Core.existentialVars, Core.coercionVars, Core.termVars, Core.body} = f $ do
  typeArgs' <- traverse resolveCoreType typeArgs
  coercionVars' <- traverse resolveCoreCoercionVarBinder coercionVars
  termVars' <- traverse resolveCoreTermVarBinder termVars
  body' <- resolveCoreExpr body
  pure
    Core.CaseArm
      { Core.implicationId,
        Core.ctor,
        Core.typeArgs = typeArgs',
        Core.existentialVars,
        Core.coercionVars = coercionVars',
        Core.termVars = termVars',
        Core.body = body'
      }
  where
    f m =
      case implicationId of
        Just id -> withImplicationId id m
        Nothing -> m

resolveCoreType :: GeneratedCoreType -> Resolve Core.CompleteType
resolveCoreType (Core.UniType u) = resolveUniVar u
resolveCoreType (Core.VarType v) = pure (Core.VarType v)
resolveCoreType (Core.ApplyType k ts) = do
  ts' <- traverse resolveCoreType ts
  pure (Core.ApplyType k ts')
resolveCoreType (Core.FamilyApplyType k ts) = do
  ts' <- traverse resolveCoreType ts
  pure (Core.FamilyApplyType k ts')
resolveCoreType (Core.ForallType v t) = do
  t' <- resolveCoreType t
  pure (Core.ForallType v t')
resolveCoreType (Core.CoercionForallType p t) = do
  p' <- resolveCoreProposition p
  t' <- resolveCoreType t
  pure (Core.CoercionForallType p' t')

resolveCoreCoercion :: GeneratedCoreCoercion -> Resolve Core.CompleteCoercion
resolveCoreCoercion (Core.UnsolvedCoercion id) = do
  c <- resolveEquality id
  resolveCoreCoercion c
resolveCoreCoercion (Core.AxiomCoercion n ts) = do
  ts' <- traverse resolveCoreType ts
  pure (Core.AxiomCoercion n ts')
resolveCoreCoercion (Core.VarCoercion v) = pure (Core.VarCoercion v)
resolveCoreCoercion (Core.TypeCtorCoercion k cs) = do
  cs' <- traverse resolveCoreCoercion cs
  pure (Core.TypeCtorCoercion k cs')
resolveCoreCoercion (Core.FamilyCoercion k cs) = do
  cs' <- traverse resolveCoreCoercion cs
  pure (Core.FamilyCoercion k cs')
resolveCoreCoercion (Core.RightCoercion n c) = do
  c' <- resolveCoreCoercion c
  pure (Core.RightCoercion n c')
resolveCoreCoercion (Core.ReflCoercion t) = do
  t' <- resolveCoreType t
  pure (Core.ReflCoercion t')
resolveCoreCoercion (Core.TransCoercion c1 c2) = do
  c1' <- resolveCoreCoercion c1
  c2' <- resolveCoreCoercion c2
  pure (Core.TransCoercion c1' c2')
resolveCoreCoercion (Core.SymmCoercion c) = do
  c' <- resolveCoreCoercion c
  pure (Core.SymmCoercion c')
resolveCoreCoercion (Core.EquivalentCoercion c1 c2) = do
  c1' <- resolveCoreCoercion c1
  c2' <- resolveCoreCoercion c2
  pure (Core.EquivalentCoercion c1' c2')
