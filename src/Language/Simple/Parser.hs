{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Simple.Parser
  ( ParseError (..),
    parseProgram,
  )
where

import Control.Applicative (Alternative (..))
import Control.Monad.Except (MonadError (..))
import Data.Attoparsec.Text (parseOnly)
import Data.Foldable (foldl')
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text, pack)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList)
import Language.Simple.Extension (Extension, extensionParser)
import Language.Simple.Syntax
  ( Binding (..),
    CaseArm (..),
    Constraint (..),
    DataCtor (..),
    DataCtorType (..),
    Expr (..),
    Monotype (..),
    Program (..),
    SimpleConstraint,
    SimpleMonotype,
    TermVar (..),
    TypeCtor (..),
    TypeScheme (..),
    TypeVar (..),
    functionType,
  )
import Language.Simple.Util (orEmpty)
import Prettyprinter (Pretty (..))
import Text.Parser.Char (alphaNum, lower, text, upper)
import Text.Parser.Combinators (choice, eof, notFollowedBy, optional, sepEndBy, try, (<?>))
import Text.Parser.Token (TokenParsing, braces, comma, commaSep, dot, parens, textSymbol, whiteSpace)

data ParseError = ParseFailed !String
  deriving (Show)

instance Pretty ParseError where
  pretty (ParseFailed s) = pretty s

parseProgram :: forall x m. (Extension x, MonadError ParseError m) => Text -> m (Program x)
parseProgram input =
  case parseOnly (programParser <* eof) input of
    Left err -> throwError $ ParseFailed err
    Right x -> pure x

programParser :: (Extension x, TokenParsing m) => m (Program x)
programParser = Program <$> lets <*> axiom <*> datum
  where
    lets = manyV (textSymbol "let" *> bindingParser)
    axiom = pure mempty
    datum = HashMap.fromList <$> many (textSymbol "data" *> dataCtorDeclParser)

dataCtorDeclParser :: (Extension x, TokenParsing m) => m (DataCtor, DataCtorType x)
dataCtorDeclParser = (,) <$> (dataCtorParser <* textSymbol "::") <*> dataCtorTypeParser

dataCtorTypeParser :: (Extension x, TokenParsing m) => m (DataCtorType x)
dataCtorTypeParser =
  DataCtorType <$> orEmpty forallQuant
    <*> orEmpty existsQuant
    <*> orEmpty qual
    <*> fieldParams
    <*> namedTypeCtorParser
    <*> manyV typeVarParser
  where
    forallQuant = textSymbol "forall" *> manyV typeVarParser <* dot
    existsQuant = textSymbol "exists" *> manyV typeVarParser <* dot
    qual = constraintParser <* textSymbol "=>"
    fieldParams = manyV (atomMonotypeParser <* textSymbol "->")

bindingParser :: (Extension x, TokenParsing m) => m (Binding x)
bindingParser =
  f <$> termVarParser
    <*> optional (textSymbol "::" *> typeSchemeParser)
    <*> (textSymbol "=" *> exprParser)
  where
    f x Nothing = UnannotatedBinding x
    f x (Just s) = AnnotatedBinding x s

exprParser :: (Extension x, TokenParsing m) => m (Expr x)
exprParser = foldl' ApplyExpr <$> atom <*> many atom <?> "expression"
  where
    atom =
      parens exprParser
        <|> lambda
        <|> case_
        <|> let_
        <|> CtorExpr <$> dataCtorParser
        <|> VarExpr <$> termVarParser
    lambda = textSymbol "\\" *> (LambdaExpr <$> (termVarParser <* dot) <*> exprParser)
    case_ = keyword "case" *> (CaseExpr <$> exprParser <*> braces (commaSepEndV caseArmParser))
    let_ =
      f <$> (keyword "let" *> termVarParser)
        <*> optional (textSymbol "::" *> typeSchemeParser)
        <*> (textSymbol "=" *> exprParser)
        <*> (keyword "in" *> exprParser)
    f x Nothing = UnannotatedLetExpr x
    f x (Just s) = AnnotatedLetExpr x s

caseArmParser :: (Extension x, TokenParsing m) => m (CaseArm x)
caseArmParser = CaseArm <$> dataCtorParser <*> manyV termVarParser <*> (textSymbol "=>" *> exprParser) <?> "case arm"

typeSchemeParser :: (Extension x, TokenParsing m) => m (TypeScheme x)
typeSchemeParser = ForallTypeScheme <$> orEmpty quant <*> orEmpty qual <*> monotypeParser <?> "type scheme"
  where
    quant = textSymbol "forall" *> manyV typeVarParser <* dot
    qual = constraintParser <* textSymbol "=>"

constraintParser :: (Extension x, TokenParsing m) => m (SimpleConstraint x)
constraintParser = foldProd <$> prod <?> "constraint"
  where
    foldProd = foldr ProductConstraint EmptyConstraint
    prod = parens (commaSep (ext <|> equal <|> constraintParser))
    equal = EqualityConstraint <$> (monotypeParser <* textSymbol "~") <*> monotypeParser
    ext = ExtensionConstraint <$> extensionParser

atomMonotypeParser :: (Extension x, TokenParsing m) => m (SimpleMonotype x)
atomMonotypeParser = skel (manyV (skel (pure mempty)))
  where
    skel arg =
      parens monotypeParser
        <|> VarType <$> typeVarParser
        <|> ApplyType <$> namedTypeCtorParser <*> arg
        <|> ExtensionType <$> extensionParser

monotypeParser :: (Extension x, TokenParsing m) => m (SimpleMonotype x)
monotypeParser = f <$> atomMonotypeParser <*> many (textSymbol "->" *> atomMonotypeParser) <?> "type"
  where
    f t [] = t
    f lhs ts = functionType lhs $ foldr1 functionType ts

keywords :: [Text]
keywords = ["let", "data", "case", "in"]

keyword :: TokenParsing m => Text -> m Text
keyword x = try (text x <* notFollowedBy alphaNum) <* whiteSpace

lowerName :: TokenParsing m => m Text
lowerName = fmap pack . try $ notFollowedBy anyKeyword *> name <* whiteSpace
  where
    name = (:) <$> lower <*> many alphaNum
    anyKeyword = choice (map keyword keywords)

upperName :: TokenParsing m => m Text
upperName = pack <$> name <* whiteSpace
  where
    name = (:) <$> upper <*> many alphaNum

typeVarParser :: TokenParsing m => m TypeVar
typeVarParser = TypeVar <$> lowerName <?> "type variable"

termVarParser :: TokenParsing m => m TermVar
termVarParser = TermVar <$> lowerName <?> "variable"

namedTypeCtorParser :: TokenParsing m => m TypeCtor
namedTypeCtorParser = NamedTypeCtor <$> upperName <?> "type constructor"

dataCtorParser :: TokenParsing m => m DataCtor
dataCtorParser = DataCtor <$> upperName <?> "data constructor"

manyV :: Alternative m => m a -> m (Vector a)
manyV = fmap Vector.fromList . many

commaSepEndV :: TokenParsing m => m a -> m (Vector a)
commaSepEndV p = Vector.fromList <$> sepEndBy p comma
