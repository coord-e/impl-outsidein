{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Simple.Type.Solver.Canonicalize
  ( canonicalizeGiven,
    canonicalizeWanted,
    isGivenCanonical,
    isWantedCanonical,
    CanonicalizeGivenOutput (..),
    CanonicalizeWantedOutput (..),
  )
where

import Control.Monad (MonadPlus (..))
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.Writer.CPS (runWriterT, tell)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (empty, member, singleton)
import Data.Vector (Vector, ifoldr, (//))
import qualified Data.Vector as Vector (fromList, izipWith, toList, zipWithM)
import qualified Language.Core.Syntax as Core
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Syntax (Monotype (..))
import Language.Simple.Type.Constraint (AtomicConstraint (..), EqualityId, GeneratedCoreCoercion, GivenConstraint (..), UniVar)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Generator (toCoreType, toCoreTypeCtor)
import Language.Simple.Type.Solver.Evidence (Evidence (..))
import Language.Simple.Type.Solver.Syntax
  ( FamilyType (..),
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
isGivenCanonical :: GivenConstraint -> Bool
isGivenCanonical (EqualityGivenConstraint _ t1@(TvType v) (FamilyFree t2)) = t1 `isSmaller` t2 && not (HashSet.member v (ftv t2))
isGivenCanonical (EqualityGivenConstraint _ (FamilyApplyType _ (FamilyFreeSeq _)) (FamilyFree _)) = True
isGivenCanonical (TypeClassGivenConstraint _ _ (FamilyFreeSeq _)) = True
isGivenCanonical _ = False

isWantedCanonical :: AtomicConstraint -> Bool
isWantedCanonical (EqualityAtomicConstraint _ t1@(TvType v) (FamilyFree t2)) = t1 `isSmaller` t2 && not (HashSet.member v (ftv t2))
isWantedCanonical (EqualityAtomicConstraint _ (FamilyApplyType _ (FamilyFreeSeq _)) (FamilyFree _)) = True
isWantedCanonical (TypeClassAtomicConstraint _ _ (FamilyFreeSeq _)) = True
isWantedCanonical _ = False

isSmaller :: Monotype UniVar -> Monotype UniVar -> Bool
isSmaller (FamilyApplyType _ _) t = not (isFamilyType t)
isSmaller (UniType _) (VarType _) = True
isSmaller (TvType v1) (TvType v2) = v1 < v2
isSmaller (TvType _) t = not (isFamilyType t) -- modified from Fig. 20
isSmaller _ _ = False

-- Fig. 21
data CanonicalizeGivenOutput = CanonicalizeGivenOutput
  { tch :: HashSet UniVar,
    flatten :: Subst UniVar,
    output :: [GivenConstraint]
  }

flattenGivenOutput :: UniVar -> FamilyType UniVar -> GivenConstraint -> CanonicalizeGivenOutput
flattenGivenOutput beta (FamilyType k ts) q = CanonicalizeGivenOutput {tch, flatten, output}
  where
    tch = HashSet.empty
    flatten = Subst.singleton beta applyTy
    output = [q, EqualityGivenConstraint (Core.ReflCoercion (toCoreType applyTy)) applyTy (UniType beta)]
    applyTy = FamilyApplyType k ts

canonicalizeGiven :: (Fresh m, MonadError TypeError m) => GivenConstraint -> MaybeT m CanonicalizeGivenOutput
canonicalizeGiven (EqualityGivenConstraint _ t1 t2)
  | syntacticEqual t1 t2 = pure $ CanonicalizeGivenOutput HashSet.empty Subst.empty []
canonicalizeGiven (EqualityGivenConstraint c t1@(ApplyType k1 ts1) t2@(ApplyType k2 ts2))
  | k1 == k2 && length ts1 == length ts2 = pure $ CanonicalizeGivenOutput HashSet.empty Subst.empty (Vector.toList (Vector.izipWith f ts1 ts2))
  | otherwise = throwError $ MismatchedTypes t1 t2
  where
    f i = EqualityGivenConstraint (Core.RightCoercion i c)
canonicalizeGiven (EqualityGivenConstraint _ t1@(TvType v) t2@(FamilyFree t))
  | HashSet.member v (ftv t) = throwError $ OccurCheckError t1 t2
canonicalizeGiven (EqualityGivenConstraint c t1 t2)
  | t2 `isSmaller` t1 = pure $ CanonicalizeGivenOutput HashSet.empty Subst.empty [EqualityGivenConstraint (Core.SymmCoercion c) t2 t1]
canonicalizeGiven (TypeClassGivenConstraint d k ts)
  | Just (fam, ctx, cctx) <- takeFamilyFreeFamilyIn ts = do
    a <- fresh
    let ec = Core.ReflCoercion (toCoreType (famToTy fam))
    let evidence = Core.CastExpr d (Core.TypeCtorCoercion (Core.ClassDictionaryTypeCtor k) (cctx ec))
    pure $ flattenGivenOutput a fam (TypeClassGivenConstraint evidence k (ctx (UniType a)))
canonicalizeGiven (EqualityGivenConstraint c (FamilyApplyType k ts) t2)
  | Just (fam, ctx, cctx) <- takeFamilyFreeFamilyIn ts = do
    a <- fresh
    let ec = Core.ReflCoercion (toCoreType (famToTy fam))
    let evidence = Core.TransCoercion (Core.SymmCoercion (Core.FamilyCoercion k (cctx ec))) c
    pure $ flattenGivenOutput a fam (EqualityGivenConstraint evidence (FamilyApplyType k (ctx (UniType a))) t2)
canonicalizeGiven (EqualityGivenConstraint c t1 t2)
  | Just (fam, ctx, cctx) <- takeFamilyFreeFamily t2,
    isFamilyType t1 || isTvType t1 -- no need to check that t1 is family-free family (that is catched in previous pattern)
    =
    do
      a <- fresh
      let ec = Core.ReflCoercion (toCoreType (famToTy fam))
      let evidence = Core.TransCoercion c (cctx ec)
      pure $ flattenGivenOutput a fam (EqualityGivenConstraint evidence t1 (ctx (UniType a)))
canonicalizeGiven _ = mzero

famToTy :: FamilyType a -> Monotype a
famToTy (FamilyType k ts) = FamilyApplyType k ts

data CanonicalizeWantedOutput = CanonicalizeWantedOutput
  { tch :: HashSet UniVar,
    flatten :: Subst UniVar,
    output :: [AtomicConstraint],
    evidence :: Evidence
  }

flattenWantedOutput :: Fresh m => UniVar -> FamilyType UniVar -> AtomicConstraint -> (EqualityId -> Evidence) -> m CanonicalizeWantedOutput
flattenWantedOutput beta (FamilyType k ts) q genEvidence = do
  id' <- fresh
  let output = [q, EqualityAtomicConstraint id' applyTy (UniType beta)]
  pure CanonicalizeWantedOutput {tch, flatten, output, evidence = genEvidence id'}
  where
    tch = HashSet.singleton beta
    flatten = Subst.empty
    applyTy = FamilyApplyType k ts

canonicalizeWanted :: (Fresh m, MonadError TypeError m) => AtomicConstraint -> MaybeT m CanonicalizeWantedOutput
canonicalizeWanted (EqualityAtomicConstraint id t1 t2)
  | syntacticEqual t1 t2 = pure $ CanonicalizeWantedOutput mempty Subst.empty mempty (EqualityEvidence id (Core.ReflCoercion (toCoreType t1)))
canonicalizeWanted (EqualityAtomicConstraint id t1@(ApplyType k1 ts1) t2@(ApplyType k2 ts2))
  | k1 == k2 && length ts1 == length ts2 = do
    (out, ids) <- runWriterT $ Vector.zipWithM f ts1 ts2
    let c = Core.TypeCtorCoercion (toCoreTypeCtor k1) (Vector.fromList (map Core.UnsolvedCoercion ids))
    pure $ CanonicalizeWantedOutput mempty Subst.empty (Vector.toList out) (EqualityEvidence id c)
  | otherwise = throwError $ MismatchedTypes t1 t2
  where
    f l r = do
      id' <- fresh
      tell [id']
      pure $ EqualityAtomicConstraint id' l r
canonicalizeWanted (EqualityAtomicConstraint _ t1@(TvType v) t2@(FamilyFree t))
  | HashSet.member v (ftv t) = throwError $ OccurCheckError t1 t2
canonicalizeWanted (EqualityAtomicConstraint id t1 t2)
  | t2 `isSmaller` t1 = do
    id' <- fresh
    let c = Core.SymmCoercion (Core.UnsolvedCoercion id')
    pure $ CanonicalizeWantedOutput mempty Subst.empty [EqualityAtomicConstraint id' t2 t1] (EqualityEvidence id c)
canonicalizeWanted (TypeClassAtomicConstraint id k ts)
  | Just (fam, ctx, cctx) <- takeFamilyFreeFamilyIn ts = do
    a <- fresh
    id' <- fresh
    let genEvidence eid = DictionaryEvidence id (Core.CastExpr (Core.UnsolvedClassDictionaryExpr id') (Core.SymmCoercion (Core.TypeCtorCoercion (Core.ClassDictionaryTypeCtor k) (cctx (Core.UnsolvedCoercion eid)))))
    flattenWantedOutput a fam (TypeClassAtomicConstraint id' k (ctx (UniType a))) genEvidence
canonicalizeWanted (EqualityAtomicConstraint id (FamilyApplyType k ts) t2)
  | Just (fam, ctx, cctx) <- takeFamilyFreeFamilyIn ts = do
    a <- fresh
    id' <- fresh
    let genEvidence eid = EqualityEvidence id (Core.TransCoercion (Core.FamilyCoercion k (cctx (Core.UnsolvedCoercion eid))) (Core.UnsolvedCoercion id'))
    flattenWantedOutput a fam (EqualityAtomicConstraint id' (FamilyApplyType k (ctx (UniType a))) t2) genEvidence
canonicalizeWanted (EqualityAtomicConstraint id t1 t2)
  | Just (fam, ctx, cctx) <- takeFamilyFreeFamily t2,
    isFamilyType t1 || isTvType t1 -- no need to check that t1 is family-free family (that is catched in previous pattern)
    =
    do
      a <- fresh
      id' <- fresh
      let genEvidence eid = EqualityEvidence id (Core.TransCoercion (Core.UnsolvedCoercion id') (Core.SymmCoercion (cctx (Core.UnsolvedCoercion eid))))
      flattenWantedOutput a fam (EqualityAtomicConstraint id' t1 (ctx (UniType a))) genEvidence
canonicalizeWanted _ = mzero

type Context t = Monotype UniVar -> t

type TypeContext = Context (Monotype UniVar)

type TypesContext = Context (Vector (Monotype UniVar))

type CoercionContext = GeneratedCoreCoercion -> GeneratedCoreCoercion

type CoercionsContext = GeneratedCoreCoercion -> Vector GeneratedCoreCoercion

takeFamilyFreeFamilyIn :: Vector (Monotype UniVar) -> Maybe (FamilyType UniVar, TypesContext, CoercionsContext)
takeFamilyFreeFamilyIn v = ifoldr f Nothing v
  where
    f i t Nothing
      | Just (fam, ctx, cctx) <- takeFamilyFreeFamily t =
        Just (fam, \r -> v // [(i, ctx r)], \c -> fmap (Core.ReflCoercion . toCoreType) v // [(i, cctx c)])
    f _ _ acc = acc

takeFamilyFreeFamily :: Monotype UniVar -> Maybe (FamilyType UniVar, TypeContext, CoercionContext)
takeFamilyFreeFamily (VarType _) = Nothing
takeFamilyFreeFamily (UniType _) = Nothing
takeFamilyFreeFamily (FamilyApplyType k ts)
  | all isFamilyFree ts = Just (FamilyType k ts, id, id)
  | otherwise = Nothing
takeFamilyFreeFamily (ApplyType k ts) = f <$> takeFamilyFreeFamilyIn ts
  where
    f (t, ctx, cctx) = (t, ApplyType k . ctx, Core.TypeCtorCoercion (toCoreTypeCtor k) . cctx)
