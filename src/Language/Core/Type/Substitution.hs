{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Core.Type.Substitution
  ( substType,
    substProposition,
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
import Language.Core.Syntax (CompleteProposition, CompleteType, Proposition (..), Type (..), TypeVar)
import Language.Simple.Fresh (Fresh (..))

newtype Subst = Subst (HashMap TypeVar CompleteType)
  deriving stock (Eq, Generic)
  deriving newtype (Show)

substType :: Fresh m => Subst -> CompleteType -> m CompleteType
substType (Subst m) (VarType v)
  | Just t <- HashMap.lookup v m = pure t
  | otherwise = pure (VarType v)
substType s (ApplyType k ts) = ApplyType k <$> mapM (substType s) ts
substType s (FamilyApplyType k ts) = FamilyApplyType k <$> mapM (substType s) ts
substType (Subst m) (ForallType v t) = do
  v' <- fresh
  ForallType v' <$> substType (Subst $ HashMap.delete v m) (refreshType v v' t)
substType s (CoercionForallType p t) = CoercionForallType <$> substProposition s p <*> substType s t

substProposition :: Fresh m => Subst -> CompleteProposition -> m CompleteProposition
substProposition s (Proposition t1 t2) = Proposition <$> substType s t1 <*> substType s t2

refreshType :: TypeVar -> TypeVar -> CompleteType -> CompleteType
refreshType v1 v2 (VarType v)
  | v == v1 = VarType v2
  | otherwise = VarType v
refreshType v1 v2 (ApplyType k ts) = ApplyType k (fmap (refreshType v1 v2) ts)
refreshType v1 v2 (FamilyApplyType k ts) = FamilyApplyType k (fmap (refreshType v1 v2) ts)
refreshType v1 v2 (ForallType v t)
  | v == v1 = ForallType v t
  | otherwise = ForallType v (refreshType v1 v2 t)
refreshType v1 v2 (CoercionForallType p t) = CoercionForallType (refreshProposition p) (refreshType v1 v2 t)
  where
    refreshProposition (Proposition t1 t2) = Proposition (refreshType v1 v2 t1) (refreshType v1 v2 t2)

fromVars :: Vector TypeVar -> Vector CompleteType -> Subst
fromVars vs ts = Subst . HashMap.fromList . Vector.toList $ Vector.zip vs ts

singleton :: TypeVar -> CompleteType -> Subst
singleton v t = Subst $ HashMap.singleton v t
