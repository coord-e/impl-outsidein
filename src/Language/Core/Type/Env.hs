{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Core.Type.Env
  ( EnvT,
    runEnvT,
    runEmptyEnvT,
    withTermVar,
    withTypeVar,
    withCoercionVar,
    lookupTermVar,
    lookupDataCtor,
    lookupAxiomScheme,
    lookupTypeVar,
    lookupCoercionVar,
  )
where

import Control.Monad.Except (MonadError)
import Control.Monad.Reader (ReaderT (..), asks, local, runReaderT)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (empty, insert, lookup)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (empty, insert, member)
import Language.Core.Syntax
  ( AxiomName,
    AxiomScheme,
    CoercionVar,
    CoercionVarBinder (..),
    DataCtor,
    DataCtorType,
    Proposition,
    TermVar,
    TermVarBinder (..),
    Type,
    TypeVar,
  )

data Env = Env
  { axioms :: HashMap AxiomName AxiomScheme,
    vars :: HashMap TermVar Type,
    dataCtors :: HashMap DataCtor DataCtorType,
    coercionVars :: HashMap CoercionVar Proposition,
    typeVars :: HashSet TypeVar
  }

newtype EnvT m a = MkEnvT (ReaderT Env m a)
  deriving newtype (Functor, Applicative, Monad, MonadError e)

withTermVar :: Monad m => TermVarBinder -> EnvT m a -> EnvT m a
withTermVar (TermVarBinder x t) (MkEnvT a) = MkEnvT $ local f a
  where
    f e@Env {vars} = e {vars = HashMap.insert x t vars}

withTypeVar :: Monad m => TypeVar -> EnvT m a -> EnvT m a
withTypeVar v (MkEnvT a) = MkEnvT $ local f a
  where
    f e@Env {typeVars} = e {typeVars = HashSet.insert v typeVars}

withCoercionVar :: Monad m => CoercionVarBinder -> EnvT m a -> EnvT m a
withCoercionVar (CoercionVarBinder v p) (MkEnvT a) = MkEnvT $ local f a
  where
    f e@Env {coercionVars} = e {coercionVars = HashMap.insert v p coercionVars}

lookupTermVar :: Monad m => TermVar -> EnvT m (Maybe Type)
lookupTermVar x = MkEnvT . asks $ HashMap.lookup x . vars

lookupDataCtor :: Monad m => DataCtor -> EnvT m (Maybe DataCtorType)
lookupDataCtor k = MkEnvT . asks $ HashMap.lookup k . dataCtors

lookupAxiomScheme :: Monad m => AxiomName -> EnvT m (Maybe AxiomScheme)
lookupAxiomScheme n = MkEnvT . asks $ HashMap.lookup n . axioms

lookupTypeVar :: Monad m => TypeVar -> EnvT m Bool
lookupTypeVar v = MkEnvT . asks $ HashSet.member v . typeVars

lookupCoercionVar :: Monad m => CoercionVar -> EnvT m (Maybe Proposition)
lookupCoercionVar v = MkEnvT . asks $ HashMap.lookup v . coercionVars

runEnvT ::
  Monad m =>
  HashMap AxiomName AxiomScheme ->
  HashMap TermVar Type ->
  HashMap DataCtor DataCtorType ->
  EnvT m a ->
  m a
runEnvT axioms vars dataCtors (MkEnvT a) = runReaderT a initEnv
  where
    initEnv =
      Env
        { vars,
          axioms,
          dataCtors,
          coercionVars = HashMap.empty,
          typeVars = HashSet.empty
        }

runEmptyEnvT :: Monad m => EnvT m a -> m a
runEmptyEnvT = runEnvT HashMap.empty HashMap.empty HashMap.empty
