{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE StrictData #-}

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
import Language.Simple.Syntax (AxiomScheme, DataCtor, DataCtorType, Monotype, TermVar, TypeScheme)
import Language.Simple.Type.Constraint (UniVar, fuv)
import Numeric.Natural (Natural)

class Monad m => HasTypeEnv m where
  lookupTermVar :: TermVar -> m (Maybe TypeScheme)
  withTermVar :: TermVar -> TypeScheme -> m a -> m a

class Monad m => HasLocalTypeEnv m where
  lookupLocalVar :: TermVar -> m (Maybe (Monotype UniVar))
  withLocalVar :: TermVar -> Monotype UniVar -> m a -> m a
  localEnvFuv :: m (HashSet UniVar)

class Monad m => HasProgramEnv m where
  lookupDataCtor :: DataCtor -> m (Maybe DataCtorType)

data Env = Env
  { vars :: HashMap TermVar TypeScheme,
    localVars :: HashMap TermVar (Monotype UniVar),
    axioms :: Vector AxiomScheme,
    dataCtors :: HashMap DataCtor DataCtorType
  }

newtype EnvT m a = MkEnvT (ReaderT Env (StateT Natural m) a)
  deriving newtype (Functor, Applicative, Monad, MonadError e, MonadLogger)

instance Monad m => HasTypeEnv (EnvT m) where
  lookupTermVar x = MkEnvT . asks $ HashMap.lookup x . vars
  withTermVar x s (MkEnvT a) = MkEnvT $ local f a
    where
      f e@Env {vars} = e {vars = HashMap.insert x s vars}

instance Monad m => HasLocalTypeEnv (EnvT m) where
  lookupLocalVar x = MkEnvT . asks $ HashMap.lookup x . localVars
  withLocalVar x t (MkEnvT a) = MkEnvT $ local f a
    where
      f e@Env {localVars} = e {localVars = HashMap.insert x t localVars}
  localEnvFuv = MkEnvT . asks $ foldMap fuv . localVars

instance Monad m => HasProgramEnv (EnvT m) where
  lookupDataCtor k = MkEnvT . asks $ HashMap.lookup k . dataCtors

instance Monad m => Fresh (EnvT m) where
  fresh = MkEnvT $ state f
    where
      f n = (fromFreshNatural n, succ n)

runEnvT :: Monad m => Vector AxiomScheme -> HashMap DataCtor DataCtorType -> EnvT m a -> m a
runEnvT axioms dataCtors (MkEnvT a) = evalStateT (runReaderT a initEnv) 0
  where
    initEnv = Env {vars = mempty, localVars = mempty, axioms, dataCtors}
