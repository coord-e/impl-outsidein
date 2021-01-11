{-# LANGUAGE DerivingStrategies #-}

module Language.Simple.Fresh
  ( Fresh (..),
    GenFresh (..),
  )
where

import Control.Monad.Except (ExceptT)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.Writer.CPS (WriterT)
import Numeric.Natural (Natural)

class Monad m => Fresh m where
  fresh :: GenFresh a => m a

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift fresh

instance Fresh m => Fresh (MaybeT m) where
  fresh = lift fresh

instance (Monoid w, Fresh m) => Fresh (WriterT w m) where
  fresh = lift fresh

class GenFresh a where
  fromFreshNatural :: Natural -> a
