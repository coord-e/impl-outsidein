{-# LANGUAGE OverloadedStrings #-}

module Util
  ( orThrow,
    orThrowM,
    foldMapM,
    orEmpty,
    firstJust,
    fromJustOr,
    logDocDebug,
    logDocInfo,
    logDocWarn,
    logDocError,
    logPretty,
    logParamsDebug,
    uncons,
    findDuplicate,
  )
where

import Control.Applicative (Alternative, optional)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (LogLevel (..), MonadLogger, logOtherN)
import Data.Foldable (fold, foldl', foldlM)
import qualified Data.HashSet as HashSet (insert, member)
import Data.Hashable (Hashable)
import Data.Vector (Vector, unsafeHead, unsafeTail)
import qualified Data.Vector as Vector (null)
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

firstJust :: Foldable f => (a -> Maybe b) -> f a -> Maybe b
firstJust f = foldl' go Nothing
  where
    go Nothing x = f x
    go (Just x) _ = Just x

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

uncons :: Vector a -> Maybe (a, Vector a)
uncons v
  | Vector.null v = Nothing
  | otherwise = Just (unsafeHead v, unsafeTail v)

findDuplicate :: (Eq a, Hashable a, Foldable f) => f a -> Maybe a
findDuplicate = snd . foldr go (mempty, Nothing)
  where
    go _ (acc, Just x) = (acc, Just x)
    go x (found, Nothing)
      | HashSet.member x found = (found, Just x)
      | otherwise = (HashSet.insert x found, Nothing)
