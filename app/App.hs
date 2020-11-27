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
import Language.Simple.ConstraintDomain (ConstraintDomain)
import Language.Simple.ConstraintDomain.SimpleUnification (SimpleUnification)
import Language.Simple.ConstraintDomain.TypeClass (TypeClass)
import Language.Simple.ConstraintDomain.TypeClassTypeFamily (TypeClassTypeFamily)
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

class ConstraintDomain x => NamedConstraintDomain x where
  constraintDomainName :: String

instance NamedConstraintDomain SimpleUnification where
  constraintDomainName = "simple"

instance NamedConstraintDomain TypeClass where
  constraintDomainName = "class"

instance NamedConstraintDomain TypeClassTypeFamily where
  constraintDomainName = "class_family"

data PackedConstraintDomain = forall x. NamedConstraintDomain x => PackedConstraintDomain (Proxy x)

availableConstraintDomains :: [PackedConstraintDomain]
availableConstraintDomains =
  [ PackedConstraintDomain (Proxy @SimpleUnification),
    PackedConstraintDomain (Proxy @TypeClass),
    PackedConstraintDomain (Proxy @TypeClassTypeFamily)
  ]

getConstraintDomain :: String -> Maybe PackedConstraintDomain
getConstraintDomain name = find f availableConstraintDomains
  where
    f (PackedConstraintDomain (Proxy :: Proxy x)) = constraintDomainName @x == name

parseProgram :: ConstraintDomain x => Text -> App x (Program x)
parseProgram = handleError . Parser.parseProgram

typeProgram :: ConstraintDomain x => Program x -> App x ()
typeProgram = handleError . Type.typeProgram

runApp :: String -> (forall x. ConstraintDomain x => App x a) -> IO a
runApp xName app = runStdoutLoggingT $
  case getConstraintDomain xName of
    Just (PackedConstraintDomain (Proxy :: Proxy x)) -> runApp' $ app @x
    Nothing -> logErrorN (docToText $ "unknown constraint domain" <+> dquotes (pretty xName)) >> liftIO exitFailure
  where
    runApp' (App a) = do
      e <- runExceptT a
      case e of
        Left errDoc -> logErrorN (docToText errDoc) >> liftIO exitFailure
        Right x -> pure x
    docToText = renderStrict . layoutPretty defaultLayoutOptions
