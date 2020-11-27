{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Simple.Extension.TypeClassTypeFamily.Syntax
  ( pattern FamilyApplyType,
    pattern TypeClassConstraint,
    pattern FamilyFree,
    pattern FamilyFreeSeq,
    pattern TvType,
    ConstraintLocation (..),
    Family (..),
    Class (..),
    FamilyType (..),
    ClassConstraint (..),
    Tv (..),
    AtomicConstraint (..),
    isFamilyType,
    isTvType,
    isFamilyFree,
    ftv,
    atomicConstraints,
    fromAtomicConstraint,
    syntacticEqual,
    syntacticEquals,
  )
where

import Control.Monad (MonadPlus (..))
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (singleton)
import Data.Hashable (Hashable)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (zip)
import GHC.Generics (Generic)
import Language.Simple.Extension.TypeClassTypeFamily.Extension
  ( Class (..),
    ExtensionConstraint (..),
    ExtensionMonotype (..),
    Family (..),
    TypeClassTypeFamily,
  )
import Language.Simple.Syntax (Constraint (..), Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (UniVar)
import Language.Simple.Type.Substitution (Substitutable (..))
import qualified Language.Simple.Type.Substitution as Subst (lookup)
import Language.Simple.Util (fromJustOr)
import Prettyprinter (Pretty (..))

type X = TypeClassTypeFamily

data ConstraintLocation
  = Wanted
  | Given

isFamilyType :: Monotype X UniVar -> Bool
isFamilyType (FamilyApplyType _ _) = True
isFamilyType _ = False

isTvType :: Monotype X UniVar -> Bool
isTvType (TvType _) = True
isTvType _ = False

pattern FamilyApplyType :: Family -> Vector (Monotype X a) -> Monotype X a
pattern FamilyApplyType k ts = ExtensionType (FamilyApplyExtensionType k ts)

{-# COMPLETE VarType, UniType, ApplyType, FamilyApplyType #-}

{-# COMPLETE TvType, ApplyType, FamilyApplyType #-}

isFamilyFree :: Monotype X a -> Bool
isFamilyFree (VarType _) = True
isFamilyFree (UniType _) = True
isFamilyFree (FamilyApplyType _ _) = False
isFamilyFree (ApplyType _ ts) = all isFamilyFree ts

familyFreeOrNothing :: Monotype X a -> Maybe (Monotype X a)
familyFreeOrNothing t
  | isFamilyFree t = Just t
  | otherwise = Nothing

pattern FamilyFree :: Monotype X a -> Monotype X a
pattern FamilyFree t <- (familyFreeOrNothing -> Just t)

pattern FamilyFreeSeq :: Traversable t => t (Monotype X a) -> t (Monotype X a)
pattern FamilyFreeSeq t <- (traverse familyFreeOrNothing -> Just t)

data FamilyType a = FamilyType Family (Vector (Monotype X a))

instance Pretty a => Pretty (FamilyType a) where
  pretty (FamilyType k ts) = pretty (FamilyApplyType k ts)

data ClassConstraint a = ClassConstraint Class (Vector (Monotype X a))

data Tv
  = UniTv UniVar
  | RigidTv TypeVar
  deriving stock (Ord, Eq, Generic, Show)
  deriving anyclass (Hashable)

tvOrNothing :: Monotype X UniVar -> Maybe Tv
tvOrNothing (UniType u) = Just (UniTv u)
tvOrNothing (VarType v) = Just (RigidTv v)
tvOrNothing _ = Nothing

pattern TvType :: Tv -> Monotype X UniVar
pattern TvType tv <-
  (tvOrNothing -> Just tv)
  where
    TvType (UniTv u) = UniType u
    TvType (RigidTv v) = VarType v

{-# COMPLETE TvType, ApplyType, ExtensionType #-}

ftv :: Monotype X UniVar -> HashSet Tv
ftv (TvType v) = HashSet.singleton v
ftv (ApplyType _ ts) = foldMap ftv ts
ftv (FamilyApplyType _ ts) = foldMap ftv ts

instance Pretty Tv where
  pretty (UniTv u) = pretty u
  pretty (RigidTv v) = pretty v

instance Substitutable X Tv (Monotype X UniVar) where
  substitute s (VarType v) = Subst.lookup (RigidTv v) s `fromJustOr` VarType v
  substitute s (UniType u) = Subst.lookup (UniTv u) s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
  substitute s (FamilyApplyType k ts) = FamilyApplyType k $ fmap (substitute s) ts

instance Substitutable X Tv (ExtensionMonotype X UniVar) where
  substitute s (FamilyApplyExtensionType k ts) = FamilyApplyExtensionType k $ fmap (substitute s) ts

instance Substitutable X Tv (ExtensionConstraint X UniVar) where
  substitute s (ClassExtensionConstraint k ts) = ClassExtensionConstraint k $ fmap (substitute s) ts

pattern TypeClassConstraint :: Class -> Vector (Monotype X a) -> Constraint X a
pattern TypeClassConstraint k ts = ExtensionConstraint (ClassExtensionConstraint k ts)

{-# COMPLETE EmptyConstraint, ProductConstraint, EqualityConstraint, TypeClassConstraint #-}

data AtomicConstraint
  = EqualityAtomicConstraint (Monotype X UniVar) (Monotype X UniVar)
  | ClassAtomicConstraint Class (Vector (Monotype X UniVar))
  deriving (Generic)

instance Pretty AtomicConstraint where
  pretty = pretty . fromAtomicConstraint

atomicConstraints :: Constraint X UniVar -> [AtomicConstraint]
atomicConstraints EmptyConstraint = mzero
atomicConstraints (ProductConstraint q1 q2) = atomicConstraints q1 `mplus` atomicConstraints q2
atomicConstraints (EqualityConstraint t1 t2) = pure $ EqualityAtomicConstraint t1 t2
atomicConstraints (TypeClassConstraint k ts) = pure $ ClassAtomicConstraint k ts

fromAtomicConstraint :: AtomicConstraint -> Constraint X UniVar
fromAtomicConstraint (EqualityAtomicConstraint t1 t2) = EqualityConstraint t1 t2
fromAtomicConstraint (ClassAtomicConstraint k ts) = TypeClassConstraint k ts

instance Substitutable X UniVar AtomicConstraint where
  substitute s (EqualityAtomicConstraint t1 t2) = EqualityAtomicConstraint (substitute s t1) (substitute s t2)
  substitute s (ClassAtomicConstraint k ts) = ClassAtomicConstraint k (fmap (substitute s) ts)

syntacticEqual :: Monotype X UniVar -> Monotype X UniVar -> Bool
syntacticEqual (UniType u1) (UniType u2) = u1 == u2
syntacticEqual (VarType v1) (VarType v2) = v1 == v2
syntacticEqual (ApplyType k1 ts1) (ApplyType k2 ts2) = k1 == k2 && syntacticEquals ts1 ts2
syntacticEqual (FamilyApplyType k1 ts1) (FamilyApplyType k2 ts2) =
  k1 == k2 && syntacticEquals ts1 ts2
syntacticEqual _ _ = False

syntacticEquals :: Vector (Monotype X UniVar) -> Vector (Monotype X UniVar) -> Bool
syntacticEquals v1 v2 = all (uncurry syntacticEqual) (Vector.zip v1 v2)
