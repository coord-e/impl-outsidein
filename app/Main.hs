module Main where

import App
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text.IO as Text (readFile)
import Language.Simple.ConstraintDomain (ConstraintDomain)
import System.Environment (getArgs)

typeFile :: ConstraintDomain x => FilePath -> App x ()
typeFile file = do
  content <- liftIO $ Text.readFile file
  program <- parseProgram content
  typeProgram program

main :: IO ()
main = do
  [x, path] <- getArgs
  runApp x $ typeFile path
