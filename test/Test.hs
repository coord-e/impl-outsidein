{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Logger (runNoLoggingT)
import Data.Functor (void)
import Data.Text (Text)
import qualified Data.Text as Text (splitOn, strip, stripPrefix, takeWhile, unpack)
import qualified Data.Text.IO as Text (readFile)
import Language.Core.Type (checkProgram)
import Language.Simple.Parser (parseProgram)
import Language.Simple.Type (typeProgram)
import Prettyprinter (Pretty (..), defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.String (renderString)
import System.Directory (listDirectory)
import System.FilePath.Posix (isExtensionOf)
import Test.Tasty
import Test.Tasty.HUnit

dataDir :: FilePath
dataDir = "test/data/"

makeTestForFile :: FilePath -> IO TestTree
makeTestForFile path = do
  content <- Text.readFile (dataDir ++ path)
  pure . testGroup path $ map (`toTest` content) (extractXNames content)
  where
    isOk = isExtensionOf "ok" path
    extractXNames =
      maybe
        ["class_family"]
        (map Text.strip . Text.splitOn ",")
        . Text.stripPrefix "// test:"
        . Text.takeWhile (/= '\n')
    toTest "class_family" = testCase "class_family" . test isOk
    toTest name = testCase (Text.unpack name <> " (skip)") . const (pure ())

test :: Bool -> Text -> Assertion
test isOk content = runNoLoggingT $ do
  program <-
    runExceptT (parseProgram content) >>= \case
      Left err -> liftIO . assertFailure $ prettyToString err
      Right x -> pure x

  runExceptT (typeProgram program) >>= \case
    Left err | isOk -> liftIO . assertFailure $ prettyToString err
    Left _ -> pure ()
    Right _ | not isOk -> liftIO $ assertFailure "unexpectedly typechecked"
    Right core -> do
      simpleCore <- assertRight $ checkProgram core
      void . assertRight $ checkProgram simpleCore
  where
    assertRight a =
      runExceptT a >>= \case
        Right x -> pure x
        Left err -> liftIO . assertFailure $ prettyToString err
    prettyToString :: Pretty a => a -> String
    prettyToString = renderString . layoutPretty defaultLayoutOptions . pretty

main :: IO ()
main = do
  files <- listDirectory dataDir
  tests <- mapM makeTestForFile files
  defaultMain $ testGroup "tests" tests
