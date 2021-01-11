module Main where

import App
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text.IO as Text (putStr, readFile)
import qualified Language.Core.Syntax as Core (printProgram)
import System.Environment (getArgs)

typeFile :: FilePath -> App ()
typeFile file = do
  content <- liftIO $ Text.readFile file
  program <- parseProgram content
  core <- typeProgram program
  liftIO . Text.putStr $ Core.printProgram core
  checkCore core

main :: IO ()
main = do
  [path] <- getArgs
  runApp $ typeFile path
