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
    applyMonotypeParser,
    monotypeParser,
    upperName,
    classParser,
    familyParser,
    lowerName,
    typeVarParser,
    namedTypeCtorParser,
    termVarParser,
    dataCtorParser,
    namedDataCtorParser,
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
import Language.Simple.Syntax
  ( AxiomScheme (..),
    Binding (..),
    CaseArm (..),
    Class (..),
    Constraint (..),
    DataCtor (..),
    DataCtorType (..),
    Expr (..),
    Family (..),
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
import Lens.Micro (_1, _2, _3, _4)
import Lens.Micro.Mtl ((%=))
import Prettyprinter (Pretty (..), (<+>))
import Text.Parser.Char (CharParsing (..), alphaNum, lower, text, upper)
import Text.Parser.Combinators
  ( Parsing (..),
    between,
    choice,
    eof,
    notFollowedBy,
    optional,
    sepEndBy,
    try,
    (<?>),
  )
import Text.Parser.Token
  ( TokenParsing (..),
    braces,
    comma,
    commaSep,
    dot,
    integer,
    parens,
    textSymbol,
    token,
    whiteSpace,
  )
import Text.Parser.Token.Style (buildSomeSpaceParser, scalaCommentStyle)
import Util (orEmpty)

data ParseError = ParseFailed !String
  deriving (Show)

instance Pretty ParseError where
  pretty (ParseFailed s) = "parse error:" <+> pretty s

parseProgram ::
  MonadError ParseError m =>
  Text ->
  m Program
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

programParser ::
  ( MonadPlus m,
    TokenParsing m
  ) =>
  m Program
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

axiomSchemeParser :: TokenParsing m => m AxiomScheme
axiomSchemeParser = ForallAxiomScheme <$> orEmpty quant <*> orEmpty qual <*> constraintParser <?> "axiom scheme"
  where
    quant = textSymbol "forall" *> manyV typeVarParser <* dot
    qual = parensConstraintParser <* textSymbol "=>"

typeDeclParser :: TokenParsing m => m (TermVar, TypeScheme)
typeDeclParser = (,) <$> (termVarParser <* textSymbol "::") <*> typeSchemeParser

dataCtorDeclParser :: TokenParsing m => m (DataCtor, DataCtorType)
dataCtorDeclParser = (,) <$> (dataCtorParser <* textSymbol "::") <*> dataCtorTypeParser

dataCtorTypeParser :: TokenParsing m => m DataCtorType
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
    fieldParams = manyV (applyMonotypeParser <* textSymbol "->")

bindingParser :: TokenParsing m => m Binding
bindingParser =
  f <$> termVarParser
    <*> optional (textSymbol "::" *> typeSchemeParser)
    <*> (textSymbol "=" *> exprParser)
  where
    f x Nothing = UnannotatedBinding x
    f x (Just s) = AnnotatedBinding x s

exprParser :: TokenParsing m => m Expr
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

caseArmParser :: TokenParsing m => m CaseArm
caseArmParser = CaseArm <$> dataCtorParser <*> manyV termVarParser <*> (textSymbol "=>" *> exprParser) <?> "case arm"

typeSchemeParser :: TokenParsing m => m TypeScheme
typeSchemeParser = ForallTypeScheme <$> orEmpty quant <*> orEmpty qual <*> monotypeParser <?> "type scheme"
  where
    quant = textSymbol "forall" *> manyV typeVarParser <* dot
    qual = parensConstraintParser <* textSymbol "=>"

parensConstraintParser :: TokenParsing m => m SimpleConstraint
parensConstraintParser = foldProd <$> prod <?> "constraint"
  where
    foldProd = foldr ProductConstraint EmptyConstraint
    prod = parens (commaSep constraintParser)

constraintParser :: TokenParsing m => m SimpleConstraint
constraintParser =
  parensConstraintParser <|> try equal <|> class_
  where
    equal = EqualityConstraint <$> (monotypeParser <* textSymbol "~") <*> monotypeParser
    class_ = TypeClassConstraint <$> classParser <*> manyV atomMonotypeParser

atomMonotypeParser :: TokenParsing m => m SimpleMonotype
atomMonotypeParser =
  parens monotypeParser
    <|> VarType <$> typeVarParser
    <|> ApplyType <$> namedTypeCtorParser <*> pure mempty
    <|> familyTypeParser

applyMonotypeParser :: TokenParsing m => m SimpleMonotype
applyMonotypeParser =
  parens monotypeParser
    <|> VarType <$> typeVarParser
    <|> ApplyType <$> namedTypeCtorParser <*> manyV atomMonotypeParser
    <|> familyTypeParser

familyTypeParser :: TokenParsing m => m SimpleMonotype
familyTypeParser = between (textSymbol "<") (textSymbol ">") inner
  where
    inner = FamilyApplyType <$> familyParser <*> manyV atomMonotypeParser

monotypeParser :: TokenParsing m => m SimpleMonotype
monotypeParser = f <$> applyMonotypeParser <*> many (textSymbol "->" *> applyMonotypeParser) <?> "type"
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

namedDataCtorParser :: TokenParsing m => m DataCtor
namedDataCtorParser = NamedDataCtor <$> upperName

dataCtorParser :: TokenParsing m => m DataCtor
dataCtorParser = IntegerDataCtor <$> integer <|> namedDataCtorParser <?> "data constructor"

classParser :: TokenParsing m => m Class
classParser = Class <$> upperName <?> "type class"

familyParser :: TokenParsing m => m Family
familyParser = Family <$> upperName <?> "type family"

manyV :: Alternative m => m a -> m (Vector a)
manyV = fmap Vector.fromList . many

commaSepEndV :: TokenParsing m => m a -> m (Vector a)
commaSepEndV p = Vector.fromList <$> sepEndBy p comma
