{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Simple.Type.Solver.Interact
  ( interactWanted,
    interactGiven,
    InteractWantedOutput (..),
  )
where

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
import Prelude hiding (interact)

-- Fig. 22
interactGiven :: Monad m => GivenConstraint -> GivenConstraint -> MaybeT m [GivenConstraint]
interactGiven q1@(EqualityGivenConstraint c1 (TvType tv1) (FamilyFree t1)) q2@(EqualityGivenConstraint c2 (TvType tv2) (FamilyFree t2))
  | tv1 == tv2 && isGivenCanonical q1 && isGivenCanonical q2 = pure [q1, EqualityGivenConstraint (Core.TransCoercion (Core.SymmCoercion c1) c2) t1 t2]
  | isGivenCanonical q1 && isGivenCanonical q2 && HashSet.member tv1 (ftv t2) =
    pure [q1, EqualityGivenConstraint (Core.TransCoercion c2 e) (TvType tv2) t2']
  where
    (t2', e) = substituteTypeWithTv c1 tv1 t1 t2
interactGiven q1@(EqualityGivenConstraint c1 (TvType tv) (FamilyFree t1)) (EqualityGivenConstraint c2 (FamilyApplyType k (FamilyFreeSeq ts)) (FamilyFree t))
  | isGivenCanonical q1 && HashSet.member tv (foldMap ftv ts <> ftv t) =
    pure [q1, EqualityGivenConstraint evidence (FamilyApplyType k ts') t']
  where
    evidence = Core.TransCoercion (Core.TransCoercion (Core.SymmCoercion (Core.FamilyCoercion k es)) c2) e
    (ts', es) = substituteTypesWithTv c1 tv t1 ts
    (t', e) = substituteTypeWithTv c1 tv t1 t
interactGiven q1@(EqualityGivenConstraint c1 (TvType tv) (FamilyFree t)) (TypeClassGivenConstraint d2 k (FamilyFreeSeq ts))
  | isGivenCanonical q1 && HashSet.member tv (foldMap ftv ts) =
    pure [q1, TypeClassGivenConstraint evidence k ts']
  where
    evidence = Core.CastExpr d2 (Core.TypeCtorCoercion (Core.ClassDictionaryTypeCtor k) es)
    (ts', es) = substituteTypesWithTv c1 tv t ts
interactGiven
  q1@(EqualityGivenConstraint c1 (FamilyApplyType k1 (FamilyFreeSeq ts1)) (FamilyFree t1))
  (EqualityGivenConstraint c2 (FamilyApplyType k2 (FamilyFreeSeq ts2)) (FamilyFree t2))
    | k1 == k2 && syntacticEquals ts1 ts2 = pure [q1, EqualityGivenConstraint (Core.TransCoercion (Core.SymmCoercion c1) c2) t1 t2]
interactGiven q1@(TypeClassGivenConstraint _ k1 (FamilyFreeSeq ts1)) (TypeClassGivenConstraint _ k2 (FamilyFreeSeq ts2))
  | k1 == k2 && syntacticEquals ts1 ts2 = pure [q1]
interactGiven _ _ = mzero

data InteractWantedOutput = InteractWantedOutput
  { rightEvidence :: Evidence,
    output :: [AtomicConstraint]
  }

interactWanted :: (Fresh m, Monad m) => AtomicConstraint -> AtomicConstraint -> MaybeT m InteractWantedOutput
interactWanted q1@(EqualityAtomicConstraint id1 (TvType tv1) (FamilyFree t1)) q2@(EqualityAtomicConstraint id2 (TvType tv2) (FamilyFree t2))
  | tv1 == tv2 && isWantedCanonical q1 && isWantedCanonical q2 = do
    id' <- fresh
    let output = [q1, EqualityAtomicConstraint id' t1 t2]
    let rightEvidence = EqualityEvidence id2 $ Core.TransCoercion (Core.UnsolvedCoercion id1) (Core.UnsolvedCoercion id')
    pure InteractWantedOutput {rightEvidence, output}
  | isWantedCanonical q1 && isWantedCanonical q2 && HashSet.member tv1 (ftv t2) = do
    id' <- fresh
    let (t2', e) = substituteTypeWithTv (Core.UnsolvedCoercion id1) tv1 t1 t2
    let output = [q1, EqualityAtomicConstraint id' (TvType tv2) t2']
    let rightEvidence = EqualityEvidence id2 $ Core.TransCoercion (Core.UnsolvedCoercion id') (Core.SymmCoercion e)
    pure InteractWantedOutput {rightEvidence, output}
interactWanted q1@(EqualityAtomicConstraint id1 (TvType tv) (FamilyFree t1)) (EqualityAtomicConstraint id2 (FamilyApplyType k (FamilyFreeSeq ts)) (FamilyFree t))
  | isWantedCanonical q1 && HashSet.member tv (foldMap ftv ts <> ftv t) = do
    id' <- fresh
    let (ts', es) = substituteTypesWithTv (Core.UnsolvedCoercion id1) tv t1 ts
    let (t', e) = substituteTypeWithTv (Core.UnsolvedCoercion id1) tv t1 t
    let output = [q1, EqualityAtomicConstraint id' (FamilyApplyType k ts') t']
    let rightEvidence = EqualityEvidence id2 $ Core.TransCoercion (Core.TransCoercion (Core.FamilyCoercion k es) (Core.UnsolvedCoercion id')) (Core.SymmCoercion e)
    pure InteractWantedOutput {rightEvidence, output}
interactWanted q1@(EqualityAtomicConstraint id1 (TvType tv) (FamilyFree t)) (TypeClassAtomicConstraint id2 k (FamilyFreeSeq ts))
  | isWantedCanonical q1 && HashSet.member tv (foldMap ftv ts) = do
    id' <- fresh
    let (ts', es) = substituteTypesWithTv (Core.UnsolvedCoercion id1) tv t ts -- sym (k es)
    let output = [q1, TypeClassAtomicConstraint id' k ts']
    let rightEvidence = DictionaryEvidence id2 $ Core.CastExpr (Core.UnsolvedClassDictionaryExpr id') (Core.SymmCoercion (Core.TypeCtorCoercion (Core.ClassDictionaryTypeCtor k) es))
    pure InteractWantedOutput {rightEvidence, output}
interactWanted
  q1@(EqualityAtomicConstraint id1 (FamilyApplyType k1 (FamilyFreeSeq ts1)) (FamilyFree t1))
  (EqualityAtomicConstraint id2 (FamilyApplyType k2 (FamilyFreeSeq ts2)) (FamilyFree t2))
    | k1 == k2 && syntacticEquals ts1 ts2 = do
      id' <- fresh
      let output = [q1, EqualityAtomicConstraint id' t1 t2]
      let rightEvidence = EqualityEvidence id2 $ Core.TransCoercion (Core.UnsolvedCoercion id1) (Core.UnsolvedCoercion id')
      pure InteractWantedOutput {rightEvidence, output}
interactWanted q1@(TypeClassAtomicConstraint id1 k1 (FamilyFreeSeq ts1)) (TypeClassAtomicConstraint id2 k2 (FamilyFreeSeq ts2))
  | k1 == k2 && syntacticEquals ts1 ts2 = pure InteractWantedOutput {rightEvidence = DictionaryEvidence id2 (Core.UnsolvedClassDictionaryExpr id1), output = [q1]}
interactWanted _ _ = mzero
