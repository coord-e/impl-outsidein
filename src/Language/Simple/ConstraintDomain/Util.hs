{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Simple.ConstraintDomain.Util
  ( Tv (..),
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
import qualified Data.Vector as Vector (zip)
import GHC.Generics (Generic)
import Language.Simple.ConstraintDomain (ExtensionConstraint, ExtensionMonotype)
import Language.Simple.Syntax (Constraint (..), Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (UniVar)
import Language.Simple.Type.Substitution (Subst (..), Substitutable (..))
import qualified Language.Simple.Type.Substitution as Subst (empty, merge, singleton)
import Prettyprinter (Pretty (..))
import Util (fromJustOr)

data Tv
  = UniTv UniVar
  | RigidTv TypeVar
  deriving stock (Show, Ord, Eq, Generic)
  deriving anyclass (Hashable)

instance Pretty Tv where
  pretty (UniTv u) = pretty u
  pretty (RigidTv v) = pretty v

instance Substitutable x Tv (ExtensionMonotype x UniVar) => Substitutable x Tv (Monotype x UniVar) where
  substitute (Subst s) (VarType v) = HashMap.lookup (RigidTv v) s `fromJustOr` VarType v
  substitute (Subst s) (UniType u) = HashMap.lookup (UniTv u) s `fromJustOr` UniType u
  substitute s (ApplyType k ts) = ApplyType k $ fmap (substitute s) ts
  substitute s (ExtensionType x) = ExtensionType $ substitute s x

isTvType :: Monotype x UniVar -> Bool
isTvType (TvType _) = True
isTvType _ = False

tvOrNothing :: Monotype x UniVar -> Maybe Tv
tvOrNothing (UniType u) = Just (UniTv u)
tvOrNothing (VarType v) = Just (RigidTv v)
tvOrNothing _ = Nothing

pattern TvType :: Tv -> Monotype x UniVar
pattern TvType tv <-
  (tvOrNothing -> Just tv)
  where
    TvType (UniTv u) = UniType u
    TvType (RigidTv v) = VarType v

{-# COMPLETE TvType, ApplyType, ExtensionType #-}

class Ftv a where
  ftv :: a -> HashSet Tv

instance Ftv (ExtensionMonotype x UniVar) => Ftv (Monotype x UniVar) where
  ftv (TvType v) = HashSet.singleton v
  ftv (ApplyType _ ts) = foldMap ftv ts
  ftv (ExtensionType x) = ftv x

instance
  ( Ftv (ExtensionMonotype x UniVar),
    Ftv (ExtensionConstraint x UniVar)
  ) =>
  Ftv (Constraint x UniVar)
  where
  ftv EmptyConstraint = HashSet.empty
  ftv (ProductConstraint q1 q2) = HashSet.union (ftv q1) (ftv q2)
  ftv (EqualityConstraint t1 t2) = HashSet.union (ftv t1) (ftv t2)
  ftv (ExtensionConstraint x) = ftv x

-- one-way matching, ignoring extension constructor

matchType :: Monotype x UniVar -> Monotype x UniVar -> Maybe (Subst x Tv)
matchType (TvType v1) (TvType v2) | v1 == v2 = Just Subst.empty
matchType (TvType v) t = Just $ Subst.singleton v t
matchType (ApplyType k1 ts1) (ApplyType k2 ts2) | k1 == k2 = matchTypes ts1 ts2
matchType _ _ = Nothing

matchTypes :: Vector (Monotype x UniVar) -> Vector (Monotype x UniVar) -> Maybe (Subst x Tv)
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
