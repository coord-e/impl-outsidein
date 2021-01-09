{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Simple.Type.Solver.Canonicalize
  ( canonicalizeGiven,
    canonicalizeWanted,
    isCanonical,
    CanonicalizeOutput (..),
  )
where

import Control.Monad (MonadPlus (..))
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans.Maybe (MaybeT)
import Data.Foldable (fold)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (member, singleton)
import Data.Vector (Vector, ifoldr, (//))
import qualified Data.Vector as Vector (zipWith)
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax (Constraint (..), Monotype (..))
import Language.Simple.Type.Constraint (UniVar)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Solver.Syntax
  ( AtomicConstraint (..),
    ConstraintLocation (..),
    FamilyType (..),
    ftv,
    isFamilyFree,
    isFamilyType,
    isTvType,
    syntacticEqual,
    pattern FamilyFree,
    pattern FamilyFreeSeq,
    pattern TvType,
  )
import Language.Simple.Type.Substitution (Subst)
import qualified Language.Simple.Type.Substitution as Subst (empty, singleton)

-- Fig. 20
isCanonical :: AtomicConstraint -> Bool
isCanonical (EqualityAtomicConstraint t1@(TvType v) (FamilyFree t2)) = t1 `isSmaller` t2 && not (HashSet.member v (ftv t2))
isCanonical (EqualityAtomicConstraint (FamilyApplyType _ (FamilyFreeSeq _)) (FamilyFree _)) = True
isCanonical (ClassAtomicConstraint _ (FamilyFreeSeq _)) = True
isCanonical _ = False

isSmaller :: Monotype UniVar -> Monotype UniVar -> Bool
isSmaller (FamilyApplyType _ _) t = not (isFamilyType t)
isSmaller (UniType _) (VarType _) = True
isSmaller (TvType v1) (TvType v2) = v1 < v2
isSmaller (TvType _) t = not (isFamilyType t) -- modified from Fig. 20
isSmaller _ _ = False

-- Fig. 21
canonicalizeGiven :: (Fresh m, MonadError TypeError m) => AtomicConstraint -> MaybeT m CanonicalizeOutput
canonicalizeGiven q = canonicalizeCommon q `mplus` canonicalizeFlatten Given q

canonicalizeWanted :: (Fresh m, MonadError TypeError m) => AtomicConstraint -> MaybeT m CanonicalizeOutput
canonicalizeWanted q = canonicalizeCommon q `mplus` canonicalizeFlatten Wanted q

data CanonicalizeOutput = CanonicalizeOutput
  { tch :: HashSet UniVar,
    flatten :: Subst UniVar,
    output :: Constraint UniVar
  }

flattenOutput :: ConstraintLocation -> UniVar -> FamilyType UniVar -> Constraint UniVar -> CanonicalizeOutput
flattenOutput l beta (FamilyType k ts) q = CanonicalizeOutput {tch = tch l, flatten = flatten l, output}
  where
    tch Wanted = HashSet.singleton beta
    tch Given = mempty
    flatten Wanted = Subst.empty
    flatten Given = Subst.singleton beta applyTy
    output = q <> EqualityConstraint applyTy (UniType beta)
    applyTy = FamilyApplyType k ts

canonicalizeFlatten :: (Fresh m, MonadError TypeError m) => ConstraintLocation -> AtomicConstraint -> MaybeT m CanonicalizeOutput
canonicalizeFlatten l (ClassAtomicConstraint k ts)
  | Just (fam, ctx) <- takeFamilyFreeFamilyIn ts = do
    a <- fresh
    pure $ flattenOutput l a fam (TypeClassConstraint k (ctx (UniType a)))
canonicalizeFlatten l (EqualityAtomicConstraint (FamilyApplyType k ts) t2)
  | Just (fam, ctx) <- takeFamilyFreeFamilyIn ts = do
    a <- fresh
    pure $ flattenOutput l a fam (EqualityConstraint (FamilyApplyType k (ctx (UniType a))) t2)
canonicalizeFlatten l (EqualityAtomicConstraint t1 t2)
  | Just (fam, ctx) <- takeFamilyFreeFamily t2,
    isFamilyType t1 || isTvType t1 -- no need to check that t1 is family-free family (that is catched in previous pattern)
    =
    do
      a <- fresh
      pure $ flattenOutput l a fam (EqualityConstraint t1 (ctx (UniType a)))
canonicalizeFlatten _ _ = mzero

canonicalizeCommon :: MonadError TypeError m => AtomicConstraint -> MaybeT m CanonicalizeOutput
canonicalizeCommon (EqualityAtomicConstraint t1 t2)
  | syntacticEqual t1 t2 = pure $ CanonicalizeOutput mempty Subst.empty mempty
canonicalizeCommon (EqualityAtomicConstraint t1@(ApplyType k1 ts1) t2@(ApplyType k2 ts2))
  | k1 == k2 && length ts1 == length ts2 = pure $ CanonicalizeOutput mempty Subst.empty (fold (Vector.zipWith EqualityConstraint ts1 ts2))
  | otherwise = throwError $ MismatchedTypes t1 t2
canonicalizeCommon (EqualityAtomicConstraint t1@(TvType v) t2@(FamilyFree t))
  | HashSet.member v (ftv t) = throwError $ OccurCheckError t1 t2
canonicalizeCommon (EqualityAtomicConstraint t1 t2)
  | t2 `isSmaller` t1 = pure $ CanonicalizeOutput mempty Subst.empty (EqualityConstraint t2 t1)
canonicalizeCommon _ = mzero

type Context t = Monotype UniVar -> t

type TypeContext = Context (Monotype UniVar)

type TypesContext = Context (Vector (Monotype UniVar))

takeFamilyFreeFamilyIn :: Vector (Monotype UniVar) -> Maybe (FamilyType UniVar, TypesContext)
takeFamilyFreeFamilyIn v = ifoldr f Nothing v
  where
    f i t Nothing | Just (fam, ctx) <- takeFamilyFreeFamily t = Just (fam, \r -> v // [(i, ctx r)])
    f _ _ acc = acc

takeFamilyFreeFamily :: Monotype UniVar -> Maybe (FamilyType UniVar, TypeContext)
takeFamilyFreeFamily (VarType _) = Nothing
takeFamilyFreeFamily (UniType _) = Nothing
takeFamilyFreeFamily (FamilyApplyType k ts)
  | all isFamilyFree ts = Just (FamilyType k ts, id)
  | otherwise = Nothing
takeFamilyFreeFamily (ApplyType k ts) = f <$> takeFamilyFreeFamilyIn ts
  where
    f (t, ctx) = (t, ApplyType k . ctx)
