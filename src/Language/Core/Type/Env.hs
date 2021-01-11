{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

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
import Control.Monad.Logger (MonadLogger)
import Control.Monad.Reader (ReaderT (..), asks, local, runReaderT)
import Control.Monad.State (StateT (..), evalStateT, state)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (empty, insert, lookup)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (empty, insert, member)
import Language.Core.Syntax
  ( AxiomName,
    AxiomScheme,
    CoercionVar,
    CoercionVarBinder (..),
    CompleteCoercionVarBinder,
    CompleteProposition,
    CompleteTermVarBinder,
    CompleteType,
    DataCtor (..),
    DataCtorType,
    TermVar,
    TermVarBinder (..),
    TypeVar,
    simpleDataCtorType,
  )
import Language.Simple.Fresh (Fresh (..), fromFreshNatural)
import Numeric.Natural (Natural)

data Env = Env
  { axioms :: HashMap AxiomName AxiomScheme,
    vars :: HashMap TermVar CompleteType,
    dataCtors :: HashMap DataCtor DataCtorType,
    coercionVars :: HashMap CoercionVar CompleteProposition,
    typeVars :: HashSet TypeVar
  }

newtype EnvT m a = MkEnvT (ReaderT Env (StateT Natural m) a)
  deriving newtype (Functor, Applicative, Monad, MonadLogger, MonadError e)

instance Monad m => Fresh (EnvT m) where
  fresh = MkEnvT $ state f
    where
      f n = (fromFreshNatural n, succ n)

withTermVar :: Monad m => CompleteTermVarBinder -> EnvT m a -> EnvT m a
withTermVar (TermVarBinder x t) (MkEnvT a) = MkEnvT $ local f a
  where
    f e@Env {vars} = e {vars = HashMap.insert x t vars}

withTypeVar :: Monad m => TypeVar -> EnvT m a -> EnvT m a
withTypeVar v (MkEnvT a) = MkEnvT $ local f a
  where
    f e@Env {typeVars} = e {typeVars = HashSet.insert v typeVars}

withCoercionVar :: Monad m => CompleteCoercionVarBinder -> EnvT m a -> EnvT m a
withCoercionVar (CoercionVarBinder v p) (MkEnvT a) = MkEnvT $ local f a
  where
    f e@Env {coercionVars} = e {coercionVars = HashMap.insert v p coercionVars}

lookupTermVar :: Monad m => TermVar -> EnvT m (Maybe CompleteType)
lookupTermVar x = MkEnvT . asks $ HashMap.lookup x . vars

boolDataCtorType :: DataCtorType
boolDataCtorType = simpleDataCtorType "Bool"

intDataCtorType :: DataCtorType
intDataCtorType = simpleDataCtorType "Int"

lookupDataCtor :: Monad m => DataCtor -> EnvT m (Maybe DataCtorType)
lookupDataCtor (NamedDataCtor "True") = pure $ Just boolDataCtorType
lookupDataCtor (NamedDataCtor "False") = pure $ Just boolDataCtorType
lookupDataCtor (IntegerDataCtor _) = pure $ Just intDataCtorType
lookupDataCtor k = MkEnvT . asks $ HashMap.lookup k . dataCtors

lookupAxiomScheme :: Monad m => AxiomName -> EnvT m (Maybe AxiomScheme)
lookupAxiomScheme n = MkEnvT . asks $ HashMap.lookup n . axioms

lookupTypeVar :: Monad m => TypeVar -> EnvT m Bool
lookupTypeVar v = MkEnvT . asks $ HashSet.member v . typeVars

lookupCoercionVar :: Monad m => CoercionVar -> EnvT m (Maybe CompleteProposition)
lookupCoercionVar v = MkEnvT . asks $ HashMap.lookup v . coercionVars

runEnvT ::
  Monad m =>
  HashMap AxiomName AxiomScheme ->
  HashMap TermVar CompleteType ->
  HashMap DataCtor DataCtorType ->
  EnvT m a ->
  m a
runEnvT axioms vars dataCtors (MkEnvT a) = evalStateT (runReaderT a initEnv) 0
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
