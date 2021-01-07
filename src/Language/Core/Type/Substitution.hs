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
import Language.Core.Syntax (Type (..), TypeVar)

newtype Subst = Subst (HashMap TypeVar Type)
  deriving stock (Eq, Generic)
  deriving newtype (Show)

substType :: Subst -> Type -> Type
substType (Subst m) (VarType v)
  | Just t <- HashMap.lookup v m = t
  | otherwise = VarType v
substType s (ApplyType k ts) = ApplyType k (fmap (substType s) ts)
substType s (FamilyType k ts) = FamilyType k (fmap (substType s) ts)
substType (Subst m) (ForallType v t) = ForallType v (substType (Subst $ HashMap.delete v m) t)
substType s (CoercionForallType b t) = CoercionForallType b (substType s t)

fromVars :: Vector TypeVar -> Vector Type -> Subst
fromVars vs ts = Subst . HashMap.fromList . Vector.toList $ Vector.zip vs ts

singleton :: TypeVar -> Type -> Subst
singleton v t = Subst $ HashMap.singleton v t
