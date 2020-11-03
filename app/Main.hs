module Main where

import App
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text.IO as Text (readFile)
import Language.Simple.Extension (Extension)
import System.Environment (getArgs)

typeFile :: Extension x => FilePath -> App x ()
typeFile file = do
  content <- liftIO $ Text.readFile file
  program <- parseProgram content
  typeProgram program

main :: IO ()
main = do
  [ext, path] <- getArgs
  runApp ext $ typeFile path
