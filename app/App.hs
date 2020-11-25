{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module App (App, runApp, parseProgram, typeProgram) where

import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Logger (LoggingT, MonadLogger, logErrorN, runStdoutLoggingT)
import Data.List (find)
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import Language.Simple.Extension (Extension)
import Language.Simple.Extension.SimpleUnification (SimpleUnification)
import Language.Simple.Extension.TypeClass (TypeClass)
import Language.Simple.Extension.TypeClassTypeFamily (TypeClassTypeFamily)
import qualified Language.Simple.Parser as Parser (parseProgram)
import Language.Simple.Syntax (Program)
import qualified Language.Simple.Type as Type (typeProgram)
import Prettyprinter (Doc, Pretty (..), defaultLayoutOptions, dquotes, layoutPretty, (<+>))
import Prettyprinter.Render.Text (renderStrict)
import System.Exit (exitFailure)

newtype App x a = App (ExceptT (Doc ()) (LoggingT IO) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadLogger)

handleError :: Pretty e => ExceptT e (App x) a -> App x a
handleError a = do
  e <- runExceptT a
  case e of
    Left err -> App (ExceptT (pure (Left (pretty err))))
    Right x -> pure x

class Extension x => NamedExtension x where
  extensionName :: String

instance NamedExtension SimpleUnification where
  extensionName = "simple"

instance NamedExtension TypeClass where
  extensionName = "class"

instance NamedExtension TypeClassTypeFamily where
  extensionName = "class_family"

data PackedExtension = forall x. NamedExtension x => PackedExtension (Proxy x)

availableExtensions :: [PackedExtension]
availableExtensions =
  [ PackedExtension (Proxy @SimpleUnification),
    PackedExtension (Proxy @TypeClass),
    PackedExtension (Proxy @TypeClassTypeFamily)
  ]

getExtension :: String -> Maybe PackedExtension
getExtension name = find f availableExtensions
  where
    f (PackedExtension (Proxy :: Proxy x)) = extensionName @x == name

parseProgram :: Extension x => Text -> App x (Program x)
parseProgram = handleError . Parser.parseProgram

typeProgram :: Extension x => Program x -> App x ()
typeProgram = handleError . Type.typeProgram

runApp :: String -> (forall x. Extension x => App x a) -> IO a
runApp extName app = runStdoutLoggingT $
  case getExtension extName of
    Just (PackedExtension (Proxy :: Proxy x)) -> runApp' $ app @x
    Nothing -> logErrorN (docToText $ "unknown extension" <+> dquotes (pretty extName)) >> liftIO exitFailure
  where
    runApp' (App a) = do
      e <- runExceptT a
      case e of
        Left errDoc -> logErrorN (docToText errDoc) >> liftIO exitFailure
        Right x -> pure x
    docToText = renderStrict . layoutPretty defaultLayoutOptions
