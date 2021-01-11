{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Simple.Type.Solver.Syntax
  ( pattern FamilyFree,
    pattern FamilyFreeSeq,
    ConstraintLocation (..),
    FamilyType (..),
    ClassConstraint (..),
    substituteTypeWithTv,
    substituteTypesWithTv,
    isFamilyType,
    isFamilyFree,
    syntacticEqual,
    syntacticEquals,
    Tv (..),
    Ftv (..),
    pattern TvType,
    isTvType,
    matchType,
    matchTypes,
  )
where

import Data.Foldable (foldlM)
import qualified Data.HashMap.Strict as HashMap (lookup)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (empty, singleton, union)
import Data.Hashable (Hashable)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (unzip, zip)
import GHC.Generics (Generic)
import qualified Language.Core.Syntax as Core
import Language.Simple.Syntax (Class, Constraint (..), Family, Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (GeneratedCoreCoercion, UniVar)
import Language.Simple.Type.Generator (toCoreTypeCtor)
import Language.Simple.Type.Substitution (Subst (..), Substitutable (..))
import qualified Language.Simple.Type.Substitution as Subst (empty, merge, singleton)
import Prettyprinter (Pretty (..))
import Util (fromJustOr)

data ConstraintLocation
  = Wanted
  | Given

isFamilyType :: Monotype UniVar -> Bool
isFamilyType (FamilyApplyType _ _) = True
isFamilyType _ = False

isFamilyFree :: Monotype a -> Bool
isFamilyFree (VarType _) = True
isFamilyFree (UniType _) = True
isFamilyFree (FamilyApplyType _ _) = False
isFamilyFree (ApplyType _ ts) = all isFamilyFree ts

familyFreeOrNothing :: Monotype a -> Maybe (Monotype a)
familyFreeOrNothing t
  | isFamilyFree t = Just t
  | otherwise = Nothing

pattern FamilyFree :: Monotype a -> Monotype a
pattern FamilyFree t <- (familyFreeOrNothing -> Just t)

pattern FamilyFreeSeq :: Traversable t => t (Monotype a) -> t (Monotype a)
pattern FamilyFreeSeq t <- (traverse familyFreeOrNothing -> Just t)

data FamilyType a = FamilyType Family (Vector (Monotype a))

instance Pretty a => Pretty (FamilyType a) where
  pretty (FamilyType k ts) = pretty (FamilyApplyType k ts)

data ClassConstraint a = ClassConstraint Class (Vector (Monotype a))

syntacticEqual :: Monotype UniVar -> Monotype UniVar -> Bool
syntacticEqual (UniType u1) (UniType u2) = u1 == u2
syntacticEqual (VarType v1) (VarType v2) = v1 == v2
syntacticEqual (ApplyType k1 ts1) (ApplyType k2 ts2) = k1 == k2 && syntacticEquals ts1 ts2
syntacticEqual (FamilyApplyType k1 ts1) (FamilyApplyType k2 ts2) =
  k1 == k2 && syntacticEquals ts1 ts2
syntacticEqual _ _ = False

syntacticEquals :: Vector (Monotype UniVar) -> Vector (Monotype UniVar) -> Bool
syntacticEquals v1 v2 = all (uncurry syntacticEqual) (Vector.zip v1 v2)

data Tv
  = UniTv UniVar
  | RigidTv TypeVar
  deriving stock (Show, Ord, Eq, Generic)
  deriving anyclass (Hashable)

instance Pretty Tv where
  pretty (UniTv u) = pretty u
  pretty (RigidTv v) = pretty v

instance Substitutable Tv (Monotype UniVar) where
  substitute (Subst s) (VarType v) = HashMap.lookup (RigidTv v) s `fromJustOr` VarType v
  substitute (Subst s) (UniType u) = HashMap.lookup (UniTv u) s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
  substitute s (FamilyApplyType k ts) = FamilyApplyType k $ fmap (substitute s) ts

isTvType :: Monotype UniVar -> Bool
isTvType (TvType _) = True
isTvType _ = False

tvOrNothing :: Monotype UniVar -> Maybe Tv
tvOrNothing (UniType u) = Just (UniTv u)
tvOrNothing (VarType v) = Just (RigidTv v)
tvOrNothing _ = Nothing

pattern TvType :: Tv -> Monotype UniVar
pattern TvType tv <-
  (tvOrNothing -> Just tv)
  where
    TvType (UniTv u) = UniType u
    TvType (RigidTv v) = VarType v

{-# COMPLETE TvType, ApplyType, FamilyApplyType #-}

class Ftv a where
  ftv :: a -> HashSet Tv

instance Ftv (Monotype UniVar) where
  ftv (TvType v) = HashSet.singleton v
  ftv (ApplyType _ ts) = foldMap ftv ts
  ftv (FamilyApplyType _ ts) = foldMap ftv ts

instance Ftv (Constraint UniVar) where
  ftv EmptyConstraint = HashSet.empty
  ftv (ProductConstraint q1 q2) = HashSet.union (ftv q1) (ftv q2)
  ftv (EqualityConstraint t1 t2) = HashSet.union (ftv t1) (ftv t2)
  ftv (TypeClassConstraint _ ts) = foldMap ftv ts

-- one-way matching

matchType :: Monotype UniVar -> Monotype UniVar -> Maybe (Subst Tv)
matchType (TvType v1) (TvType v2) | v1 == v2 = Just Subst.empty
matchType (TvType v) t = Just $ Subst.singleton v t
matchType (ApplyType k1 ts1) (ApplyType k2 ts2) | k1 == k2 = matchTypes ts1 ts2
matchType (FamilyApplyType k1 ts1) (FamilyApplyType k2 ts2) | k1 == k2 = matchTypes ts1 ts2
matchType _ _ = Nothing

matchTypes :: Vector (Monotype UniVar) -> Vector (Monotype UniVar) -> Maybe (Subst Tv)
matchTypes ts1 ts2
  | length ts1 == length ts2 = foldlM go Subst.empty $ Vector.zip ts1 ts2
  | otherwise = Nothing
  where
    go s1 (t1, t2) = do
      s2 <- matchType t1 t2
      Subst.merge TvType simpleEqual s1 s2
    simpleEqual (TvType v1) (TvType v2) = v1 == v2
    simpleEqual (ApplyType k1 ts1') (ApplyType k2 ts2') = k1 == k2 && simpleEquals ts1' ts2'
    simpleEqual _ _ = False
    simpleEquals v1 v2 = all (uncurry simpleEqual) (Vector.zip v1 v2)

-- substitute `v` with `t1` in `t2` witnessed by `c1 :: TvType tv ~ t1` to `t3` and construct `c2 :: t2 ~ t3` using `c1`
-- where `(t3, c2) = substituteTypeWithTv c1 tv t1 t2`
substituteTypeWithTv :: GeneratedCoreCoercion -> Tv -> Monotype UniVar -> Monotype UniVar -> (Monotype UniVar, GeneratedCoreCoercion)
substituteTypeWithTv c tv t (VarType v)
  | tv == RigidTv v = (t, c)
  | otherwise = (VarType v, Core.ReflCoercion (Core.VarType v))
substituteTypeWithTv c tv t (UniType u)
  | tv == UniTv u = (t, c)
  | otherwise = (UniType u, Core.ReflCoercion (Core.UniType u))
substituteTypeWithTv c tv t (ApplyType k ts) = (ApplyType k ts', Core.TypeCtorCoercion (toCoreTypeCtor k) cs)
  where
    (ts', cs) = substituteTypesWithTv c tv t ts
substituteTypeWithTv c tv t (FamilyApplyType k ts) = (FamilyApplyType k ts', Core.FamilyCoercion k cs)
  where
    (ts', cs) = substituteTypesWithTv c tv t ts

substituteTypesWithTv :: GeneratedCoreCoercion -> Tv -> Monotype UniVar -> Vector (Monotype UniVar) -> (Vector (Monotype UniVar), Vector GeneratedCoreCoercion)
substituteTypesWithTv c tv t ts = Vector.unzip $ fmap (substituteTypeWithTv c tv t) ts
