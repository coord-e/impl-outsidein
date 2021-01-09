{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Core.Type.Substitution
  ( substType,
    Subst (..),
    fromVars,
    singleton,
  )
where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (delete, fromList, lookup, singleton)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (toList, zip)
import GHC.Generics (Generic)
import Language.Core.Syntax (CompleteType, Type (..), TypeVar)

newtype Subst = Subst (HashMap TypeVar CompleteType)
  deriving stock (Eq, Generic)
  deriving newtype (Show)

substType :: Subst -> CompleteType -> CompleteType
substType (Subst m) (VarType v)
  | Just t <- HashMap.lookup v m = t
  | otherwise = VarType v
substType s (ApplyType k ts) = ApplyType k (fmap (substType s) ts)
substType s (FamilyApplyType k ts) = FamilyApplyType k (fmap (substType s) ts)
substType (Subst m) (ForallType v t) = ForallType v (substType (Subst $ HashMap.delete v m) t)
substType s (CoercionForallType b t) = CoercionForallType b (substType s t)

fromVars :: Vector TypeVar -> Vector CompleteType -> Subst
fromVars vs ts = Subst . HashMap.fromList . Vector.toList $ Vector.zip vs ts

singleton :: TypeVar -> CompleteType -> Subst
singleton v t = Subst $ HashMap.singleton v t
