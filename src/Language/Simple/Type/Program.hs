{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-error=unused-imports #-}
{-# OPTIONS_GHC -Wno-error=unused-top-binds #-}

module Language.Simple.Type.Program
  ( typeProgram,
  )
where

import Control.Monad (unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Control.Monad.State (runStateT, state)
import qualified Data.HashMap.Strict as HashMap (elems, empty, fromList, insert, lookup, map, size)
import Data.Maybe (mapMaybe)
import Data.Text (Text, pack)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, toList)
import Data.Void (vacuous)
import qualified Language.Core.Syntax as Core
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax
  ( AxiomScheme (..),
    Binding (..),
    Class,
    Constraint (..),
    DataCtorType (..),
    Monotype (..),
    Program (..),
    SimpleConstraint,
    SimpleMonotype,
    TermVar,
    TypeScheme (..),
    TypeVar (..),
  )
import Language.Simple.Type.Constraint
  ( AtomicConstraint (..),
    AxiomSchemeId (..),
    DictionaryId,
    EqualityId,
    Fuv (..),
    GeneratedConstraint (..),
    GeneratedCoreExpr,
    GeneratedCoreType,
    UniVar,
  )
import Language.Simple.Type.Env (HasLocalTypeEnv (..), HasProgramEnv, HasTypeEnv (..), runBuiltinT, runEnvT)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Generator
  ( applyGivenToExpr,
    applyGivenToType,
    applyGivenTypesToType,
    applyTypeScheme,
    generateConstraint,
    newEquality,
    toCompleteCoreType,
    toCoreType,
    toCoreTypeCtor,
  )
import Language.Simple.Type.Resolve (resolveCore, resolveType)
import Language.Simple.Type.Solver (ResultingUnifier (..), solveConstraint)
import Language.Simple.Type.Solver.Evidence (Evidence (..), EvidenceStore, addEvidence, emptyEvidenceStore, makeAxiomName, makeDictionaryVar, unionEvidenceStore)
import Language.Simple.Type.Substitution (Subst (..), Substitutable (..), Unifier)
import qualified Language.Simple.Type.Substitution as Subst (compose)
import Numeric (showIntAtBase)
import Prettyprinter (Pretty (..), nest, (<+>))
import Util (logDocInfo)

typeProgram ::
  ( MonadLogger m,
    MonadError TypeError m
  ) =>
  Program ->
  m Core.Program
typeProgram Program {bindings, axioms, vars, dataCtors} = do
  coreBindings <- runEnvT (HashMap.fromList axiomsWithId) vars dataCtors . runBuiltinT $ foldr go (pure []) bindings
  pure
    Core.Program
      { bindings = Vector.fromList coreBindings,
        axioms = HashMap.fromList (mapMaybe toCoreAxiom axiomsWithId),
        vars = HashMap.fromList (mapMaybe toCoreDictVar axiomsWithId) <> HashMap.map toCoreTypeScheme vars,
        dataCtors = HashMap.map toCoreDataCtorType dataCtors
      }
  where
    go binding acc = do
      (b, x, s) <- typeBinding binding
      bs <- withTermVar x s acc
      pure (b : bs)
    axiomsWithId = zip (map AxiomSchemeId [0 ..]) $ Vector.toList axioms
    toCoreAxiom (id, ForallAxiomScheme {vars = vars', constraint = EmptyConstraint, head = EqualityConstraint (FamilyApplyType k ts) rhs}) =
      Just (makeAxiomName id, Core.ForallAxiomScheme {vars = vars', lhs = toCompleteCoreType (FamilyApplyType k ts), rhs = toCompleteCoreType rhs})
    toCoreAxiom _ = Nothing
    toCoreDictVar (id, ForallAxiomScheme {vars = vars', constraint, head = TypeClassConstraint k ts}) =
      Just (makeDictionaryVar id, applyGivenTypesToType vars' (extractPropositions constraint) (extractDictTypes constraint) dictType)
      where
        dictType = Core.ApplyType (Core.ClassDictionaryTypeCtor k) (fmap toCompleteCoreType ts)
    toCoreDictVar _ = Nothing
    toCoreDataCtorType DataCtorType {universalVars, existentialVars, constraint, fields, ctor, ctorArgs} =
      Core.DataCtorType
        { universalVars,
          existentialVars,
          coercionVars = Vector.fromList (extractPropositions constraint),
          fields = Vector.fromList (extractDictTypes constraint) <> fmap toCompleteCoreType fields,
          ctor = toCoreTypeCtor ctor,
          ctorArgs
        }
    toCoreTypeScheme ForallTypeScheme {vars = vars', constraint, monotype} =
      applyGivenTypesToType vars' (extractPropositions constraint) (extractDictTypes constraint) (toCompleteCoreType monotype)
    extractPropositions EmptyConstraint = []
    extractPropositions (ProductConstraint c1 c2) = extractPropositions c1 <> extractPropositions c2
    extractPropositions (EqualityConstraint t1 t2) = [Core.Proposition (toCompleteCoreType t1) (toCompleteCoreType t2)]
    extractPropositions (TypeClassConstraint _ _) = []
    extractDictTypes EmptyConstraint = []
    extractDictTypes (ProductConstraint c1 c2) = extractDictTypes c1 <> extractDictTypes c2
    extractDictTypes (TypeClassConstraint k ts) = [Core.ApplyType (Core.ClassDictionaryTypeCtor k) (fmap toCompleteCoreType ts)]
    extractDictTypes (EqualityConstraint _ _) = []

typeBinding ::
  ( HasLocalTypeEnv m,
    HasTypeEnv m,
    HasProgramEnv m,
    Fresh m,
    MonadLogger m,
    MonadError TypeError m
  ) =>
  Binding ->
  m (Core.Binding, TermVar, TypeScheme)
typeBinding (UnannotatedBinding x e) = do
  -- Generate
  a <- UniType <$> fresh
  (e', t, c) <- withLocalVar x a $ generateConstraint e
  (fCo, fQ) <- newEquality a t
  -- Solve
  let c' = c <> AtomicGeneratedConstraint fQ
  let tch = fuv t <> fuv c'
  (q, u@ResultingUnifier {simples}, evidences) <- solveConstraint mempty tch c'
  let t' = substitute simples t
  unless (null q || not (null (fuv q))) $ throwError (UnresolvedConstraint q)
  -- Generalize
  (s, coreTy, outE, paramUnifier, paramEvidence) <- generalizeToTypeScheme q t' (Core.CastExpr e' fCo)
  let u' = addUnifier paramUnifier u
  let outE' = resolveCore (unionEvidenceStore paramEvidence evidences) u' outE
  let coreTy' = resolveType u' coreTy
  let binding = Core.Binding (Core.TermVarBinder x coreTy') outE'
  logDocInfo $ "typed unannotated binding" <+> pretty x <+> "::" <+> nest 2 (pretty s)
  pure (binding, x, s)
typeBinding (AnnotatedBinding x s@ForallTypeScheme {monotype} e) = do
  -- Generate
  (e', v, c) <- withTermVar x s $ generateConstraint e
  (fCo, fQ) <- newEquality v (vacuous monotype)
  (given, coreTy, outE) <- applyTypeScheme s (Core.CastExpr e' fCo)
  -- Solve
  let tch = fuv v <> fuv c
  let c' = c <> AtomicGeneratedConstraint fQ
  (q, u, evidences) <- solveConstraint given tch c'
  unless (null q) $ throwError (UnresolvedConstraint q)
  let outE' = resolveCore evidences u outE
  let coreTy' = resolveType u coreTy
  let binding = Core.Binding (Core.TermVarBinder x coreTy') outE'
  logDocInfo $ "typed annotated binding" <+> pretty x <+> "::" <+> nest 2 (pretty s)
  pure (binding, x, s)

addUnifier :: Unifier -> ResultingUnifier -> ResultingUnifier
addUnifier unifier u@ResultingUnifier {simples} = u {simples = Subst.compose unifier simples}

data SimpleAtomicConstraint
  = EqualitySimpleAtomicConstraint EqualityId SimpleMonotype SimpleMonotype
  | TypeClassSimpleAtomicConstraint DictionaryId Class (Vector SimpleMonotype)

fromSimpleAtomicConstraint :: SimpleAtomicConstraint -> SimpleConstraint
fromSimpleAtomicConstraint (EqualitySimpleAtomicConstraint _ t1 t2) = EqualityConstraint t1 t2
fromSimpleAtomicConstraint (TypeClassSimpleAtomicConstraint _ k ts) = TypeClassConstraint k ts

generalizeToTypeScheme ::
  (Fresh m, Monad m) =>
  [AtomicConstraint] ->
  Monotype UniVar ->
  GeneratedCoreExpr ->
  m (TypeScheme, GeneratedCoreType, GeneratedCoreExpr, Unifier, EvidenceStore)
generalizeToTypeScheme qs t e = do
  ((constraint, monotype), vars) <- flip runStateT HashMap.empty $ do
    qs' <- traverse generalizeAtomicConstraint qs
    t' <- generalizeType t
    pure (qs', t')
  (coercionVars, equalityEvidences) <- unzip . concat <$> traverse takeEquality constraint
  (dictFields, dictionaryEvidences) <- unzip . concat <$> traverse takeDictionary constraint
  let t' = applyGivenToType (HashMap.elems vars) coercionVars dictFields (toCoreType (vacuous monotype))
  let e' = applyGivenToExpr (HashMap.elems vars) coercionVars dictFields e
  let unifier = Subst (HashMap.map VarType vars)
  let evidences = foldr addEvidence (foldr addEvidence emptyEvidenceStore equalityEvidences) dictionaryEvidences
  let scheme =
        ForallTypeScheme
          { vars = Vector.fromList (HashMap.elems vars),
            constraint = toConstraint constraint,
            monotype
          }
  pure (scheme, t', e', unifier, evidences)
  where
    takeEquality (EqualitySimpleAtomicConstraint id t1 t2) = do
      c <- fresh
      let evidence = EqualityEvidence id (Core.VarCoercion c)
      let binder = Core.CoercionVarBinder c (Core.Proposition (simpleToCoreType t1) (simpleToCoreType t2))
      pure [(binder, evidence)]
    takeEquality TypeClassSimpleAtomicConstraint {} = pure []
    takeDictionary (TypeClassSimpleAtomicConstraint id k ts) = do
      d <- fresh
      let evidence = DictionaryEvidence id (Core.VarExpr d)
      let binder = Core.TermVarBinder d (Core.ApplyType (Core.ClassDictionaryTypeCtor k) (fmap simpleToCoreType ts))
      pure [(binder, evidence)]
    takeDictionary EqualitySimpleAtomicConstraint {} = pure []
    simpleToCoreType = toCoreType . vacuous
    gen = state . f
    f u m =
      case HashMap.lookup u m of
        Just v -> (v, m)
        Nothing -> (v, HashMap.insert u v m)
          where
            v = nextVar m
    nextVar = TypeVar . intToName . HashMap.size
    generalizeType (UniType u) = VarType <$> gen u
    generalizeType (VarType v) = pure $ VarType v
    generalizeType (ApplyType k ts) = ApplyType k <$> traverse generalizeType ts
    generalizeType (FamilyApplyType k ts) = FamilyApplyType k <$> traverse generalizeType ts
    generalizeAtomicConstraint (EqualityAtomicConstraint id t1 t2) = EqualitySimpleAtomicConstraint id <$> generalizeType t1 <*> generalizeType t2
    generalizeAtomicConstraint (TypeClassAtomicConstraint id k ts) = TypeClassSimpleAtomicConstraint id k <$> traverse generalizeType ts
    toConstraint [] = EmptyConstraint
    toConstraint cs = foldr1 ProductConstraint (map fromSimpleAtomicConstraint cs)

intToName :: Int -> Text
intToName i = pack str
  where
    str = showIntAtBase base (chars !!) i ""
    base = toEnum (length chars)
    chars = ['a' .. 'z']
