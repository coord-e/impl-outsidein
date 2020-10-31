{-# LANGUAGE DerivingStrategies #-}

module Language.Simple.Fresh
  ( Fresh (..),
    GenFresh (..),
  )
where

import Control.Monad.Except (ExceptT)
import Control.Monad.Trans (lift)
import Numeric.Natural (Natural)

class Monad m => Fresh m where
  fresh :: GenFresh a => m a

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift fresh

class GenFresh a where
  fromFreshNatural :: Natural -> a
