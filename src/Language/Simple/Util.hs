{-# LANGUAGE OverloadedStrings #-}

module Language.Simple.Util
  ( orThrow,
    orThrowM,
    foldMapM,
    orEmpty,
    fromJustOr,
    logDocDebug,
    logDocInfo,
    logDocWarn,
    logDocError,
    logPretty,
    logParamsDebug,
  )
where

import Control.Applicative (Alternative, optional)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (LogLevel (..), MonadLogger, logOtherN)
import Data.Foldable (fold, foldlM)
import Prettyprinter
  ( Doc,
    Pretty (..),
    comma,
    defaultLayoutOptions,
    layoutPretty,
    line,
    nest,
    pretty,
    punctuate,
    sep,
    (<+>),
  )
import Prettyprinter.Render.Text (renderStrict)

orThrow :: MonadError e m => Maybe a -> e -> m a
orThrow (Just x) _ = pure x
orThrow Nothing e = throwError e

orThrowM :: MonadError e m => m (Maybe a) -> e -> m a
orThrowM a e = do
  m <- a
  m `orThrow` e

foldMapM :: (Monad m, Monoid w, Foldable t) => (a -> m w) -> t a -> m w
foldMapM f = foldlM g mempty
  where
    g acc x = do
      w <- f x
      pure $ acc <> w

orEmpty :: (Alternative f, Monoid a) => f a -> f a
orEmpty a = fold <$> optional a

fromJustOr :: Maybe a -> a -> a
fromJustOr (Just x) _ = x
fromJustOr Nothing x = x

logDoc :: MonadLogger m => LogLevel -> Doc ann -> m ()
logDoc level doc = logOtherN level text
  where
    text = renderStrict (layoutPretty defaultLayoutOptions doc)

logPretty :: (Pretty a, MonadLogger m) => LogLevel -> a -> m ()
logPretty level = logDoc level . pretty

logDocDebug, logDocInfo, logDocWarn, logDocError :: MonadLogger m => Doc ann -> m ()
logDocDebug = logDoc LevelDebug
logDocInfo = logDoc LevelInfo
logDocWarn = logDoc LevelWarn
logDocError = logDoc LevelError

logParamsDebug :: MonadLogger m => Doc ann -> [(Doc ann, Doc ann)] -> m ()
logParamsDebug msg [] = logDocDebug msg
logParamsDebug msg ((ht, hd) : t) = logDocDebug $ msg <> nest 2 paramsDoc
  where
    paramsDoc = sep (punctuate comma (line <> ht <> ":" <+> nest 2 hd : map f t))
    f (name, doc) = name <> ":" <+> nest 2 doc
