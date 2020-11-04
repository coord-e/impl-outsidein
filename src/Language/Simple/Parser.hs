{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Simple.Parser
  ( ParseError (..),
    parseProgram,

    -- * Parsers
    programParser,
    dataCtorDeclParser,
    dataCtorTypeParser,
    bindingParser,
    exprParser,
    caseArmParser,
    typeSchemeParser,
    constraintParser,
    parensConstraintParser,
    atomMonotypeParser,
    monotypeParser,
    upperName,
    lowerName,
    typeVarParser,
    namedTypeCtorParser,
    termVarParser,
    dataCtorParser,
  )
where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus (..))
import Control.Monad.Except (MonadError (..))
import Control.Monad.State (execStateT)
import Data.Attoparsec.Text (parseOnly)
import Data.Foldable (foldl')
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text, pack)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList)
import Language.Simple.Extension (Extension, extensionParser)
import Language.Simple.Syntax
  ( AxiomScheme (..),
    Binding (..),
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
import Lens.Micro (_1, _2, _3, _4)
import Lens.Micro.Mtl ((%=))
import Prettyprinter (Pretty (..), (<+>))
import Text.Parser.Char (CharParsing (..), alphaNum, lower, text, upper)
import Text.Parser.Combinators (Parsing (..), choice, eof, notFollowedBy, optional, sepEndBy, try, (<?>))
import Text.Parser.Token (TokenParsing (..), braces, comma, commaSep, dot, parens, textSymbol, token, whiteSpace)
import Text.Parser.Token.Style (buildSomeSpaceParser, scalaCommentStyle)

data ParseError = ParseFailed !String
  deriving (Show)

instance Pretty ParseError where
  pretty (ParseFailed s) = "parse error:" <+> pretty s

parseProgram :: forall x m. (Extension x, MonadError ParseError m) => Text -> m (Program x)
parseProgram input =
  case parseOnly (runComment (whiteSpace *> programParser <* eof)) input of
    Left err -> throwError $ ParseFailed err
    Right x -> pure x

newtype Comment m a = Comment {runComment :: m a}
  deriving newtype (Functor, Applicative, Alternative, Monad, MonadPlus, Parsing, CharParsing)

instance TokenParsing m => TokenParsing (Comment m) where
  someSpace = buildSomeSpaceParser (Comment someSpace) scalaCommentStyle
  nesting (Comment p) = Comment $ nesting p
  semi = Comment semi
  highlight h (Comment p) = Comment $ highlight h p

programParser :: (Extension x, MonadPlus m, TokenParsing m) => m (Program x)
programParser = makeProgram <$> execStateT (many toplevel) mempty
  where
    toplevel =
      choice
        [ textSymbol "let" *> bindingParser >>= cons _1,
          textSymbol "axiom" *> axiomSchemeParser >>= cons _2,
          textSymbol "type" *> typeDeclParser >>= cons _3,
          textSymbol "data" *> dataCtorDeclParser >>= cons _4
        ]
    cons l x = l %= (x :)
    makeProgram (b, a, v, d) =
      Program (Vector.fromList b) (Vector.fromList a) (HashMap.fromList v) (HashMap.fromList d)

axiomSchemeParser :: (Extension x, TokenParsing m) => m (AxiomScheme x)
axiomSchemeParser = ForallAxiomScheme <$> orEmpty quant <*> orEmpty qual <*> constraintParser <?> "axiom scheme"
  where
    quant = textSymbol "forall" *> manyV typeVarParser <* dot
    qual = parensConstraintParser <* textSymbol "=>"

typeDeclParser :: (Extension x, TokenParsing m) => m (TermVar, TypeScheme x)
typeDeclParser = (,) <$> (termVarParser <* textSymbol "::") <*> typeSchemeParser

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
    qual = parensConstraintParser <* textSymbol "=>"
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
    qual = parensConstraintParser <* textSymbol "=>"

parensConstraintParser :: (Extension x, TokenParsing m) => m (SimpleConstraint x)
parensConstraintParser = foldProd <$> prod <?> "constraint"
  where
    foldProd = foldr ProductConstraint EmptyConstraint
    prod = parens (commaSep constraintParser)

constraintParser :: (Extension x, TokenParsing m) => m (SimpleConstraint x)
constraintParser =
  -- `try` is carelessly placed here to parse typeclass-like constraint in `ext`
  parensConstraintParser <|> try equal <|> ext
  where
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
keywords = ["let", "data", "case", "in", "axiom", "type"]

keyword :: TokenParsing m => Text -> m Text
keyword x = token . try $ text x <* notFollowedBy alphaNum

lowerName :: TokenParsing m => m Text
lowerName = fmap pack . token . try $ notFollowedBy anyKeyword *> name
  where
    name = (:) <$> lower <*> many alphaNum
    anyKeyword = choice (map keyword keywords)

upperName :: TokenParsing m => m Text
upperName = pack <$> token name
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
