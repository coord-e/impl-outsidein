module Main where

import App
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text.IO as Text (readFile)
import System.Environment (getArgs)

typeFile :: FilePath -> App ()
typeFile file = do
  content <- liftIO $ Text.readFile file
  program <- parseProgram content
  typeProgram program

main :: IO ()
main = do
  [path] <- getArgs
  runApp $ typeFile path
