{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Simple.Type.Solver.TopReact
  ( topReactGiven,
    topReactWanted,
    TopReactGivenOutput (..),
    TopReactWantedOutput (..),
  )
where

import Control.Monad (MonadPlus (..), forM_)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Foldable (foldl')
import qualified Data.HashMap.Strict as HashMap (elems, toList, union)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (empty, member, singleton)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (filter)
import Data.Void (Void, vacuous)
import qualified Language.Core.Syntax as Core
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax (AxiomScheme (..), Constraint (..), Monotype (..), TypeVar)
import Language.Simple.Type.Constraint
  ( AtomicConstraint (..),
    GeneratedCoreCoercion,
    GeneratedCoreType,
    GivenConstraint (..),
    UniVar,
    fuv,
  )
import Language.Simple.Type.Env (HasProgramEnv (..))
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Generator (applyConstraints, atomicConstraints, toCoreType)
import Language.Simple.Type.Solver.Evidence (Evidence (..), makeAxiomName, makeDictionaryVar)
import Language.Simple.Type.Solver.Syntax
  ( ClassConstraint (..),
    FamilyType (..),
    Tv (..),
    matchTypes,
    pattern FamilyFree,
    pattern FamilyFreeSeq,
  )
import Language.Simple.Type.Substitution (Subst (..), substitute)
import qualified Language.Simple.Type.Substitution as Subst (fromBinders, lookup)
import Util (findDuplicate, firstJust)
import Prelude hiding (head)

data TopReactGivenOutput = TopReactGivenOutput
  { tch :: HashSet UniVar,
    output :: [GivenConstraint]
  }

topReactGiven :: (HasProgramEnv m, Fresh m, MonadError TypeError m) => GivenConstraint -> MaybeT m TopReactGivenOutput
topReactGiven (EqualityGivenConstraint c (FamilyApplyType k (FamilyFreeSeq ts)) (FamilyFree t)) = do
  TopReactFamilyOutput {axiomCoercion, rhs} <- topReactFamily (FamilyType k ts)
  let c' = Core.TransCoercion (Core.SymmCoercion axiomCoercion) c
  pure TopReactGivenOutput {tch = HashSet.empty, output = [EqualityGivenConstraint c' rhs t]}
topReactGiven q@(TypeClassGivenConstraint _ k (FamilyFreeSeq ts)) = do
  MatchingClassAxiom {} <- findMatchingClassAxiom (ClassConstraint k ts)
  throwError $ MatchingGivenConstraint q
topReactGiven _ = mzero

data TopReactWantedOutput = TopReactWantedOutput
  { tch :: HashSet UniVar,
    output :: [AtomicConstraint],
    evidence :: Evidence
  }

topReactWanted :: (HasProgramEnv m, Fresh m, MonadError TypeError m) => AtomicConstraint -> MaybeT m TopReactWantedOutput
topReactWanted (EqualityAtomicConstraint id (FamilyApplyType k (FamilyFreeSeq ts)) (FamilyFree t)) = do
  TopReactFamilyOutput {axiomCoercion, wantedTch = tch, rhs} <- topReactFamily (FamilyType k ts)
  id' <- fresh
  let evidence = EqualityEvidence id (Core.TransCoercion axiomCoercion (Core.UnsolvedCoercion id'))
  pure TopReactWantedOutput {tch, output = [EqualityAtomicConstraint id' rhs t], evidence}
topReactWanted (TypeClassAtomicConstraint id k (FamilyFreeSeq ts)) = do
  MatchingClassAxiom {dictVar, vars, onlyPredicateVars, predicate, subst = Subst subst} <- findMatchingClassAxiom (ClassConstraint k ts)
  Subst onlyPredicateSubst <- Subst.fromBinders $ fmap RigidTv onlyPredicateVars
  -- TODO: deal with raw subst manipulation
  let subst' = Subst $ HashMap.union subst onlyPredicateSubst
  let predicate' = substitute subst' (vacuous predicate)
  output <- atomicConstraints predicate'
  let tch = foldMap fuv $ HashMap.elems onlyPredicateSubst
  let dictExpr = foldl' Core.TypeApplyExpr (Core.VarExpr dictVar) (toTypeArgs subst' vars)
  let evidence = DictionaryEvidence id $ applyConstraints output dictExpr
  pure TopReactWantedOutput {tch, output, evidence}
topReactWanted _ = mzero

data TopReactFamilyOutput = TopReactFamilyOutput
  { axiomCoercion :: GeneratedCoreCoercion,
    wantedTch :: HashSet UniVar,
    rhs :: Monotype UniVar
  }

topReactFamily ::
  ( HasProgramEnv m,
    MonadError TypeError m,
    Fresh m
  ) =>
  FamilyType UniVar ->
  MaybeT m TopReactFamilyOutput
topReactFamily fam = do
  MatchingFamilyAxiom {axiomName, vars, onlyRhsVars, rhs, subst = Subst subst} <- findMatchingFamilyAxiom fam
  Subst onlyRhsSubst <- Subst.fromBinders $ fmap RigidTv onlyRhsVars
  -- TODO: deal with raw subst manipulation
  let subst' = Subst $ HashMap.union subst onlyRhsSubst
  let rhs' = substitute subst' (vacuous rhs)
  let axiomCoercion = Core.AxiomCoercion axiomName (toTypeArgs subst' vars)
  let wantedTch = foldMap fuv (HashMap.elems onlyRhsSubst)
  pure TopReactFamilyOutput {axiomCoercion, wantedTch, rhs = rhs'}

toTypeArgs :: Subst Tv -> Vector TypeVar -> Vector GeneratedCoreType
toTypeArgs subst = fmap f
  where
    f v = case Subst.lookup (RigidTv v) subst of
      Just t -> toCoreType t
      Nothing -> Core.VarType v

data MatchingClassAxiom = MatchingClassAxiom
  { dictVar :: Core.TermVar,
    vars :: Vector TypeVar,
    onlyPredicateVars :: Vector TypeVar,
    predicate :: Constraint Void,
    subst :: Subst Tv
  }

findMatchingClassAxiom ::
  ( HasProgramEnv m,
    MonadError TypeError m
  ) =>
  ClassConstraint UniVar ->
  MaybeT m MatchingClassAxiom
findMatchingClassAxiom cls = do
  schemes <- lift getAxiomSchemes
  (id, vars, ts0, predicate, subst) <- MaybeT . pure . firstJust go $ HashMap.toList schemes
  forM_ (findDuplicate vars) $ throwError . ConflictingTypeVars
  let onlyPredicateVars = Vector.filter (not . (`HashSet.member` foldMap frv ts0)) vars
  pure MatchingClassAxiom {dictVar = makeDictionaryVar id, vars, onlyPredicateVars, predicate, subst}
  where
    go (id, ForallAxiomScheme {vars, constraint, head = TypeClassConstraint k0 (FamilyFreeSeq ts0)})
      | Just subst <- matchClass (ClassConstraint k0 ts0) cls =
        Just (id, vars, ts0, constraint, subst)
    go (_, ForallAxiomScheme {}) = Nothing

data MatchingFamilyAxiom = MatchingFamilyAxiom
  { axiomName :: Core.AxiomName,
    vars :: Vector TypeVar,
    onlyRhsVars :: Vector TypeVar,
    rhs :: Monotype Void,
    subst :: Subst Tv
  }

findMatchingFamilyAxiom ::
  ( HasProgramEnv m,
    MonadError TypeError m
  ) =>
  FamilyType UniVar ->
  MaybeT m MatchingFamilyAxiom
findMatchingFamilyAxiom fam = do
  schemes <- lift getAxiomSchemes
  (id, vars, ts0, rhs, subst) <- MaybeT . pure . firstJust go $ HashMap.toList schemes
  forM_ (findDuplicate vars) $ throwError . ConflictingTypeVars
  let onlyRhsVars = Vector.filter (not . (`HashSet.member` foldMap frv ts0)) vars
  pure MatchingFamilyAxiom {axiomName = makeAxiomName id, vars, onlyRhsVars, rhs, subst}
  where
    go
      ( id,
        ForallAxiomScheme
          { vars,
            constraint = EmptyConstraint,
            head = EqualityConstraint (FamilyApplyType k0 (FamilyFreeSeq ts0)) rhs
          }
        )
        | Just subst <- matchFamily (FamilyType k0 ts0) fam =
          Just (id, vars, ts0, rhs, subst)
    go (_, ForallAxiomScheme {}) = Nothing

frv :: Monotype Void -> HashSet TypeVar
frv (VarType v) = HashSet.singleton v
frv (ApplyType _ ts) = foldMap frv ts
frv (FamilyApplyType _ ts) = foldMap frv ts

matchClass :: ClassConstraint Void -> ClassConstraint UniVar -> Maybe (Subst Tv)
matchClass (ClassConstraint k1 ts1) (ClassConstraint k2 ts2)
  | k1 == k2 = matchTypes (fmap vacuous ts1) ts2
  | otherwise = Nothing

matchFamily :: FamilyType Void -> FamilyType UniVar -> Maybe (Subst Tv)
matchFamily (FamilyType k1 ts1) (FamilyType k2 ts2)
  | k1 == k2 = matchTypes (fmap vacuous ts1) ts2
  | otherwise = Nothing
