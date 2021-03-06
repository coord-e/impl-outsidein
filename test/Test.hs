{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Logger (runNoLoggingT)
import Data.Text (Text)
import qualified Data.Text as Text (splitOn, strip, stripPrefix, takeWhile, unpack)
import qualified Data.Text.IO as Text (readFile)
import Language.Simple.ConstraintDomain (ConstraintDomain)
import Language.Simple.ConstraintDomain.SimpleUnification (SimpleUnification)
import Language.Simple.ConstraintDomain.TypeClass (TypeClass)
import Language.Simple.ConstraintDomain.TypeClassTypeFamily (TypeClassTypeFamily)
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
        (map fst names)
        (map Text.strip . Text.splitOn ",")
        . Text.stripPrefix "// test:"
        . Text.takeWhile (/= '\n')
    toTest name =
      case lookup name names of
        Just p -> testCase (Text.unpack name) . p isOk
        Nothing -> error $ "unknown constraint domain " ++ show name
    names =
      [ ("simple", test @SimpleUnification),
        ("class", test @TypeClass),
        ("class_family", test @TypeClassTypeFamily)
      ]

test :: forall x. ConstraintDomain x => Bool -> Text -> Assertion
test isOk content = runNoLoggingT $ do
  program <-
    runExceptT (parseProgram @x content) >>= \case
      Left err -> liftIO . assertFailure $ prettyToString err
      Right x -> pure x

  runExceptT (typeProgram program) >>= \case
    Left err | isOk -> liftIO . assertFailure $ prettyToString err
    Right () | not isOk -> liftIO $ assertFailure "unexpectedly typechecked"
    _ -> pure ()
  where
    prettyToString :: Pretty a => a -> String
    prettyToString = renderString . layoutPretty defaultLayoutOptions . pretty

main :: IO ()
main = do
  files <- listDirectory dataDir
  tests <- mapM makeTestForFile files
  defaultMain $ testGroup "tests" tests
