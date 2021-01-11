{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Simple.Type.Solver.Simplify (simplify, SimplifyOutput (..)) where

import Control.Monad (MonadPlus (..))
import Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.HashSet as HashSet (member)
import qualified Language.Core.Syntax as Core
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax (Monotype (..))
import Language.Simple.Type.Constraint (AtomicConstraint (..), GivenConstraint (..))
import Language.Simple.Type.Solver.Canonicalize (isGivenCanonical, isWantedCanonical)
import Language.Simple.Type.Solver.Evidence (Evidence (..))
import Language.Simple.Type.Solver.Syntax
  ( ftv,
    substituteTypeWithTv,
    substituteTypesWithTv,
    syntacticEquals,
    pattern FamilyFree,
    pattern FamilyFreeSeq,
    pattern TvType,
  )

data SimplifyOutput = SimplifyOutput
  { evidence :: Evidence,
    output :: [AtomicConstraint]
  }

simplify :: (Fresh m, Monad m) => GivenConstraint -> AtomicConstraint -> MaybeT m SimplifyOutput
simplify q1@(EqualityGivenConstraint c (TvType tv1) (FamilyFree t1)) q2@(EqualityAtomicConstraint id (TvType tv2) (FamilyFree t2))
  | tv1 == tv2 && isGivenCanonical q1 && isWantedCanonical q2 = do
    id' <- fresh
    let output = [EqualityAtomicConstraint id' t1 t2]
    let evidence = EqualityEvidence id $ Core.TransCoercion c (Core.UnsolvedCoercion id')
    pure SimplifyOutput {evidence, output}
  | isGivenCanonical q1 && isWantedCanonical q2 && HashSet.member tv1 (ftv t2) = do
    id' <- fresh
    let (t2', e) = substituteTypeWithTv c tv1 t1 t2
    let output = [EqualityAtomicConstraint id' (TvType tv2) t2']
    let evidence = EqualityEvidence id $ Core.TransCoercion (Core.UnsolvedCoercion id') (Core.SymmCoercion e)
    pure SimplifyOutput {evidence, output}
simplify q1@(EqualityGivenConstraint c (TvType tv) (FamilyFree t1)) (EqualityAtomicConstraint id (FamilyApplyType k (FamilyFreeSeq ts)) (FamilyFree t))
  | isGivenCanonical q1 && HashSet.member tv (foldMap ftv ts) = do
    id' <- fresh
    let (ts', es) = substituteTypesWithTv c tv t1 ts
    let output = [EqualityAtomicConstraint id' (FamilyApplyType k ts') t]
    let evidence = EqualityEvidence id $ Core.TransCoercion (Core.FamilyCoercion k es) (Core.UnsolvedCoercion id')
    pure SimplifyOutput {evidence, output}
simplify q1@(EqualityGivenConstraint c (TvType tv) (FamilyFree t)) (TypeClassAtomicConstraint id k (FamilyFreeSeq ts))
  | isGivenCanonical q1 && HashSet.member tv (foldMap ftv ts) = do
    id' <- fresh
    let (ts', es) = substituteTypesWithTv c tv t ts
    let output = [TypeClassAtomicConstraint id' k ts']
    let evidence = DictionaryEvidence id $ Core.CastExpr (Core.UnsolvedClassDictionaryExpr id') (Core.SymmCoercion (Core.TypeCtorCoercion (Core.ClassDictionaryTypeCtor k) es))
    pure SimplifyOutput {evidence, output}
simplify
  (EqualityGivenConstraint c (FamilyApplyType k1 (FamilyFreeSeq ts1)) (FamilyFree t1))
  (EqualityAtomicConstraint id (FamilyApplyType k2 (FamilyFreeSeq ts2)) (FamilyFree t2))
    | k1 == k2 && syntacticEquals ts1 ts2 = do
      id' <- fresh
      let output = [EqualityAtomicConstraint id' t1 t2]
      let evidence = EqualityEvidence id $ Core.TransCoercion c (Core.UnsolvedCoercion id')
      pure SimplifyOutput {evidence, output}
simplify (TypeClassGivenConstraint d k1 (FamilyFreeSeq ts1)) (TypeClassAtomicConstraint id k2 (FamilyFreeSeq ts2))
  | k1 == k2 && syntacticEquals ts1 ts2 = pure SimplifyOutput {evidence = DictionaryEvidence id d, output = []}
simplify _ _ = mzero
