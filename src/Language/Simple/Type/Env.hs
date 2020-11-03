{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Simple.Type.Env
  ( HasTypeEnv (..),
    HasLocalTypeEnv (..),
    HasProgramEnv (..),
    EnvT,
    runEnvT,
  )
where

import Control.Monad.Except (MonadError)
import Control.Monad.Logger (MonadLogger)
import Control.Monad.Reader (ReaderT (..), asks, local, runReaderT)
import Control.Monad.State (StateT (..), evalStateT, state)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (insert, lookup)
import Data.HashSet (HashSet)
import Data.Vector (Vector)
import Language.Simple.Fresh (Fresh (..), fromFreshNatural)
import Language.Simple.Syntax (AxiomScheme, DataCtor, DataCtorType, ExtensionMonotype, Monotype, TermVar, TypeScheme)
import Language.Simple.Type.Constraint (Fuv (..), UniVar)
import Numeric.Natural (Natural)

class Monad m => HasTypeEnv x m | m -> x where
  lookupTermVar :: TermVar -> m (Maybe (TypeScheme x))
  withTermVar :: TermVar -> TypeScheme x -> m a -> m a

class Monad m => HasLocalTypeEnv x m | m -> x where
  lookupLocalVar :: TermVar -> m (Maybe (Monotype x UniVar))
  withLocalVar :: TermVar -> Monotype x UniVar -> m a -> m a
  localEnvFuv :: m (HashSet UniVar)

class Monad m => HasProgramEnv x m | m -> x where
  lookupDataCtor :: DataCtor -> m (Maybe (DataCtorType x))
  getAxiomSchemes :: m (Vector (AxiomScheme x))

data Env x = Env
  { vars :: HashMap TermVar (TypeScheme x),
    localVars :: HashMap TermVar (Monotype x UniVar),
    axioms :: Vector (AxiomScheme x),
    dataCtors :: HashMap DataCtor (DataCtorType x)
  }

newtype EnvT x m a = MkEnvT (ReaderT (Env x) (StateT Natural m) a)
  deriving newtype (Functor, Applicative, Monad, MonadError e, MonadLogger)

instance Monad m => HasTypeEnv x (EnvT x m) where
  lookupTermVar x = MkEnvT . asks $ HashMap.lookup x . vars
  withTermVar x s (MkEnvT a) = MkEnvT $ local f a
    where
      f e@Env {vars} = e {vars = HashMap.insert x s vars}

instance (Fuv (ExtensionMonotype x UniVar), Monad m) => HasLocalTypeEnv x (EnvT x m) where
  lookupLocalVar x = MkEnvT . asks $ HashMap.lookup x . localVars
  withLocalVar x t (MkEnvT a) = MkEnvT $ local f a
    where
      f e@Env {localVars} = e {localVars = HashMap.insert x t localVars}
  localEnvFuv = MkEnvT . asks $ foldMap fuv . localVars

instance Monad m => HasProgramEnv x (EnvT x m) where
  lookupDataCtor k = MkEnvT . asks $ HashMap.lookup k . dataCtors
  getAxiomSchemes = MkEnvT $ asks axioms

instance Monad m => Fresh (EnvT x m) where
  fresh = MkEnvT $ state f
    where
      f n = (fromFreshNatural n, succ n)

runEnvT :: Monad m => Vector (AxiomScheme x) -> HashMap DataCtor (DataCtorType x) -> EnvT x m a -> m a
runEnvT axioms dataCtors (MkEnvT a) = evalStateT (runReaderT a initEnv) 0
  where
    initEnv = Env {vars = mempty, localVars = mempty, axioms, dataCtors}
