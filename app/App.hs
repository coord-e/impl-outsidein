{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module App (App, runApp, handleError) where

import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Logger (LoggingT, MonadLogger, logErrorN, runStdoutLoggingT)
import Prettyprinter (Doc, Pretty (..), defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.Text (renderStrict)
import System.Exit (exitFailure)

newtype App a = App (ExceptT (Doc ()) (LoggingT IO) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadLogger)

handleError :: Pretty e => ExceptT e App a -> App a
handleError a = do
  e <- runExceptT a
  case e of
    Left err -> App (ExceptT (pure (Left (pretty err))))
    Right x -> pure x

runApp :: App a -> IO a
runApp (App a) = runStdoutLoggingT $ do
  e <- runExceptT a
  case e of
    Left errDoc -> logErrorN (docToText errDoc) >> liftIO exitFailure
    Right x -> pure x
  where
    docToText = renderStrict . layoutPretty defaultLayoutOptions
