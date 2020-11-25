{-# LANGUAGE PatternSynonyms #-}

module Language.Simple.Extension.TypeClassTypeFamily.Interact (interact) where

import Control.Monad (MonadPlus (..))
import Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.HashSet as HashSet (member)
import Language.Simple.Extension.TypeClassTypeFamily.Canonicalize (isCanonical)
import Language.Simple.Extension.TypeClassTypeFamily.Extension (TypeClassTypeFamily)
import Language.Simple.Extension.TypeClassTypeFamily.Syntax
  ( AtomicConstraint (..),
    fromAtomicConstraint,
    ftv,
    syntacticEquals,
    pattern FamilyApplyType,
    pattern FamilyFree,
    pattern FamilyFreeSeq,
    pattern TvType,
  )
import Language.Simple.Syntax (Constraint (..))
import Language.Simple.Type.Constraint (UniVar)
import Language.Simple.Type.Substitution (substitute)
import qualified Language.Simple.Type.Substitution as Subst (singleton)
import Prelude hiding (interact)

type X = TypeClassTypeFamily

-- Fig. 22
interact :: Monad m => AtomicConstraint -> AtomicConstraint -> MaybeT m (Constraint X UniVar)
interact q1@(EqualityAtomicConstraint (TvType tv1) (FamilyFree t1)) q2@(EqualityAtomicConstraint (TvType tv2) (FamilyFree t2))
  | tv1 == tv2 && isCanonical q1 && isCanonical q2 = pure $ fromAtomicConstraint q1 <> EqualityConstraint t1 t2
  | isCanonical q1 && isCanonical q2 && HashSet.member tv1 (ftv t2) =
    pure $ fromAtomicConstraint q1 <> EqualityConstraint (TvType tv2) (substitute (Subst.singleton tv1 t1) t2)
interact q1@(EqualityAtomicConstraint (TvType tv) (FamilyFree t1)) q2@(EqualityAtomicConstraint (FamilyApplyType _ (FamilyFreeSeq ts)) (FamilyFree t))
  | isCanonical q1 && HashSet.member tv (foldMap ftv ts <> ftv t) =
    pure $ fromAtomicConstraint q1 <> substitute (Subst.singleton tv t1) (fromAtomicConstraint q2)
interact q1@(EqualityAtomicConstraint (TvType tv) (FamilyFree t)) q2@(ClassAtomicConstraint _ (FamilyFreeSeq ts))
  | isCanonical q1 && HashSet.member tv (foldMap ftv ts) =
    pure $ fromAtomicConstraint q1 <> substitute (Subst.singleton tv t) (fromAtomicConstraint q2)
interact
  q1@(EqualityAtomicConstraint (FamilyApplyType k1 (FamilyFreeSeq ts1)) (FamilyFree t1))
  (EqualityAtomicConstraint (FamilyApplyType k2 (FamilyFreeSeq ts2)) (FamilyFree t2))
    | k1 == k2 && syntacticEquals ts1 ts2 = pure $ fromAtomicConstraint q1 <> EqualityConstraint t1 t2
interact q1@(ClassAtomicConstraint k1 (FamilyFreeSeq ts1)) (ClassAtomicConstraint k2 (FamilyFreeSeq ts2))
  | k1 == k2 && syntacticEquals ts1 ts2 = pure $ fromAtomicConstraint q1
interact _ _ = mzero
