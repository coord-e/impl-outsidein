{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Simple.Extension
  ( Extension (..),
    SyntaxExtension (..),
    ExtensionConstraint,
    ExtensionMonotype,
    ExtensionTypeError,
    Generalizable (..),
    Instantiable (..),
  )
where

import Control.Monad.Except (MonadError)
import Data.HashSet (HashSet)
import Data.Void (Void)
import Language.Simple.Fresh (Fresh)
import Language.Simple.Syntax (Constraint (..), ExtensionConstraint, ExtensionMonotype, Monotype (..), SimpleMonotype, TypeVar)
import Language.Simple.Type.Constraint (Fuv (..), UniVar)
import Language.Simple.Type.Env (HasProgramEnv)
import Language.Simple.Type.Error (ExtensionTypeError, TypeError)
import Language.Simple.Type.Substitution (Substitutable (..), Unifier)
import Prettyprinter (Pretty (..))
import Text.Parser.Token (TokenParsing)

class
  ( SyntaxExtension x (ExtensionMonotype x),
    SyntaxExtension x (ExtensionConstraint x),
    Pretty (ExtensionTypeError x)
  ) =>
  Extension x
  where
  simplifyConstraint ::
    ( Fresh m,
      HasProgramEnv x m,
      MonadError (TypeError x) m
    ) =>
    Constraint x UniVar ->
    HashSet UniVar ->
    Constraint x UniVar ->
    m (Constraint x UniVar, Unifier x)

class
  ( Functor f,
    Fuv (f UniVar),
    Pretty (f Void),
    Pretty (f UniVar),
    Generalizable x f,
    Instantiable x f,
    Substitutable x UniVar (f UniVar)
  ) =>
  SyntaxExtension x f
    | f -> x
  where
  extensionParser :: TokenParsing m => m (f Void)

class Generalizable x f | f -> x where
  generalize :: Applicative m => (UniVar -> m (SimpleMonotype x)) -> f UniVar -> m (f Void)

instance Generalizable x (ExtensionMonotype x) => Generalizable x (Monotype x) where
  generalize f (UniType u) = f u
  generalize _ (VarType v) = pure $ VarType v
  generalize f (ApplyType k ts) = ApplyType k <$> traverse (generalize f) ts
  generalize f (ExtensionType x) = ExtensionType <$> generalize f x

instance
  ( Generalizable x (ExtensionMonotype x),
    Generalizable x (ExtensionConstraint x)
  ) =>
  Generalizable x (Constraint x)
  where
  generalize _ EmptyConstraint = pure EmptyConstraint
  generalize f (ProductConstraint q1 q2) = ProductConstraint <$> generalize f q1 <*> generalize f q2
  generalize f (EqualityConstraint t1 t2) = EqualityConstraint <$> generalize f t1 <*> generalize f t2
  generalize f (ExtensionConstraint x) = ExtensionConstraint <$> generalize f x

class Instantiable x f | f -> x where
  instantiate :: Applicative m => (TypeVar -> m (Monotype x UniVar)) -> f Void -> m (f UniVar)

instance Instantiable x (ExtensionMonotype x) => Instantiable x (Monotype x) where
  instantiate f (VarType v) = f v
  instantiate f (ApplyType k ts) = ApplyType k <$> traverse (instantiate f) ts
  instantiate f (ExtensionType x) = ExtensionType <$> instantiate f x

instance
  ( Instantiable x (ExtensionMonotype x),
    Instantiable x (ExtensionConstraint x)
  ) =>
  Instantiable x (Constraint x)
  where
  instantiate _ EmptyConstraint = pure EmptyConstraint
  instantiate f (ProductConstraint q1 q2) = ProductConstraint <$> instantiate f q1 <*> instantiate f q2
  instantiate f (EqualityConstraint t1 t2) = EqualityConstraint <$> instantiate f t1 <*> instantiate f t2
  instantiate f (ExtensionConstraint x) = ExtensionConstraint <$> instantiate f x
