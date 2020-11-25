{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Simple.Extension.TypeClassTypeFamily.Extension
  ( TypeClassTypeFamily,
    ExtensionMonotype (..),
    ExtensionConstraint (..),
    ExtensionTypeError (..),
    Class (..),
    Family (..),
  )
where

import Control.Applicative (Alternative (..))
import Data.Hashable (Hashable)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, toList)
import GHC.Generics (Generic)
import Language.Simple.Extension
  ( ExtensionConstraint,
    ExtensionMonotype,
    Generalizable (..),
    Instantiable (..),
    SyntaxExtension (..),
  )
import Language.Simple.Parser (atomMonotypeParser, upperName)
import Language.Simple.Syntax (Constraint, Monotype (..), TypeVar, prettyAtomMonotype)
import Language.Simple.Type.Constraint (Fuv (..), UniVar)
import Language.Simple.Type.Error (ExtensionTypeError)
import Language.Simple.Type.Substitution (Substitutable (..))
import Prettyprinter (Pretty (..), hsep, (<+>))
import Prettyprinter.Internal (unsafeTextWithoutNewlines)
import Text.Parser.Combinators (between)
import Text.Parser.Token (TokenParsing, textSymbol)
import Prelude hiding (head)

data TypeClassTypeFamily

type X = TypeClassTypeFamily

newtype Class = Class Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty Class where
  pretty (Class x) = unsafeTextWithoutNewlines x

classParser :: TokenParsing m => m Class
classParser = Class <$> upperName

newtype Family = Family Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty Family where
  pretty (Family x) = unsafeTextWithoutNewlines x

familyParser :: TokenParsing m => m Family
familyParser = Family <$> upperName

data instance ExtensionMonotype X a
  = FamilyApplyExtensionType Family (Vector (Monotype X a))

instance Functor (ExtensionMonotype X) where
  fmap f (FamilyApplyExtensionType k ts) = FamilyApplyExtensionType k $ fmap (fmap f) ts

instance Fuv (ExtensionMonotype X UniVar) where
  fuv (FamilyApplyExtensionType _ ts) = foldMap fuv ts

instance Pretty a => Pretty (ExtensionMonotype X a) where
  pretty (FamilyApplyExtensionType k ts) = "<" <> inner <> ">"
    where
      inner = hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))

instance Generalizable X (ExtensionMonotype X) where
  generalize f (FamilyApplyExtensionType k ts) = FamilyApplyExtensionType k <$> traverse (generalize f) ts

instance Instantiable X (ExtensionMonotype X) where
  instantiate f (FamilyApplyExtensionType k ts) = FamilyApplyExtensionType k <$> traverse (instantiate f) ts

instance Substitutable X UniVar (ExtensionMonotype X UniVar) where
  substitute s (FamilyApplyExtensionType k ts) = FamilyApplyExtensionType k $ fmap (substitute s) ts

instance Substitutable X TypeVar (ExtensionMonotype X UniVar) where
  substitute s (FamilyApplyExtensionType k ts) = FamilyApplyExtensionType k $ fmap (substitute s) ts

instance SyntaxExtension X (ExtensionMonotype X) where
  extensionParser = between (textSymbol "<") (textSymbol ">") inner
    where
      inner = FamilyApplyExtensionType <$> familyParser <*> manyV atomMonotypeParser

data instance ExtensionConstraint X a
  = ClassExtensionConstraint Class (Vector (Monotype X a))

instance Functor (ExtensionConstraint X) where
  fmap f (ClassExtensionConstraint k ts) = ClassExtensionConstraint k $ fmap (fmap f) ts

instance Fuv (ExtensionConstraint X UniVar) where
  fuv (ClassExtensionConstraint _ ts) = foldMap fuv ts

instance Pretty a => Pretty (ExtensionConstraint X a) where
  pretty (ClassExtensionConstraint k ts) = hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))

instance Generalizable X (ExtensionConstraint X) where
  generalize f (ClassExtensionConstraint k ts) = ClassExtensionConstraint k <$> traverse (generalize f) ts

instance Instantiable X (ExtensionConstraint X) where
  instantiate f (ClassExtensionConstraint k ts) = ClassExtensionConstraint k <$> traverse (instantiate f) ts

instance Substitutable X UniVar (ExtensionConstraint X UniVar) where
  substitute s (ClassExtensionConstraint k ts) = ClassExtensionConstraint k $ fmap (substitute s) ts

instance Substitutable X TypeVar (ExtensionConstraint X UniVar) where
  substitute s (ClassExtensionConstraint k ts) = ClassExtensionConstraint k $ fmap (substitute s) ts

instance SyntaxExtension X (ExtensionConstraint X) where
  extensionParser = ClassExtensionConstraint <$> classParser <*> manyV atomMonotypeParser

data instance ExtensionTypeError X = MatchingGivenConstraint (Constraint X UniVar)

instance Pretty (ExtensionTypeError X) where
  pretty (MatchingGivenConstraint q) = "the constraint" <+> pretty q <+> "matches an instance declaration"

manyV :: Alternative m => m a -> m (Vector a)
manyV = fmap Vector.fromList . many
