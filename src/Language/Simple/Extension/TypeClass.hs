{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Simple.Extension.TypeClass
  ( TypeClass,
    Class (..),
  )
where

import Control.Applicative (empty, many)
import Control.Monad.Except (MonadError (..))
import Data.Hashable (Hashable)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, null, toList)
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Simple.Extension
  ( Extension (..),
    ExtensionConstraint,
    ExtensionMonotype,
    ExtensionTypeError,
    Generalizable (..),
    Instantiable (..),
    SyntaxExtension (..),
  )
import Language.Simple.Extension.SimpleUnification
  ( SimpleUnification,
    Tv,
    simplifyUnificationConstraint,
    toXConstraint,
  )
import qualified Language.Simple.Extension.SimpleUnification as U (ExtensionTypeError (..), toXType)
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Parser (atomMonotypeParser, upperName)
import Language.Simple.Syntax (AxiomScheme (..), Constraint (..), Monotype (..), TypeVar, prettyAtomMonotype)
import Language.Simple.Type.Constraint (Fuv (..), UniVar)
import Language.Simple.Type.Env (HasProgramEnv (..))
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Subst (..), Substitutable (..), Unifier)
import qualified Language.Simple.Type.Substitution as Subst (compose, empty, fromBinders, null, replace, singleton)
import Language.Simple.Util (findDuplicate, foldMapM, uncons)
import Prettyprinter (Pretty (..), hsep, squotes, (<+>))
import Prettyprinter.Internal (unsafeTextWithoutNewlines)
import Text.Parser.Token (TokenParsing)
import Prelude hiding (head)

data TypeClass

type X = TypeClass

newtype Class = Class Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty Class where
  pretty (Class x) = unsafeTextWithoutNewlines x

classParser :: TokenParsing m => m Class
classParser = Class <$> upperName

data instance ExtensionMonotype X a

-- hlint can't parse EmptyCase without {}
{- ORMOLU_DISABLE -}
discardMonotypeExt :: ExtensionMonotype X a -> b
discardMonotypeExt x = case x of {}
{- ORMOLU_ENABLE -}

instance Functor (ExtensionMonotype X) where
  fmap _ = discardMonotypeExt

instance Fuv (ExtensionMonotype X a) where
  fuv = discardMonotypeExt

instance Pretty (ExtensionMonotype X a) where
  pretty = discardMonotypeExt

instance Generalizable X (ExtensionMonotype X) where
  generalize _ = discardMonotypeExt

instance Instantiable X (ExtensionMonotype X) where
  instantiate _ = discardMonotypeExt

instance Substitutable X UniVar (ExtensionMonotype X a) where
  substitute _ = discardMonotypeExt

instance SyntaxExtension X (ExtensionMonotype X) where
  extensionParser = empty

data instance ExtensionConstraint X a
  = TypeClassConstraint Class (Vector (Monotype X a))

instance Functor (ExtensionConstraint X) where
  fmap f (TypeClassConstraint k ts) = TypeClassConstraint k $ fmap (fmap f) ts

instance Fuv (ExtensionConstraint X UniVar) where
  fuv (TypeClassConstraint _ ts) = foldMap fuv ts

instance Pretty a => Pretty (ExtensionConstraint X a) where
  pretty (TypeClassConstraint k ts) = hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))

instance Generalizable X (ExtensionConstraint X) where
  generalize f (TypeClassConstraint k ts) = TypeClassConstraint k <$> traverse (generalize f) ts

instance Instantiable X (ExtensionConstraint X) where
  instantiate f (TypeClassConstraint k ts) = TypeClassConstraint k <$> traverse (instantiate f) ts

instance Substitutable X UniVar (ExtensionConstraint X UniVar) where
  substitute s (TypeClassConstraint k ts) = TypeClassConstraint k $ fmap (substitute s) ts

instance SyntaxExtension X (ExtensionConstraint X) where
  extensionParser = TypeClassConstraint <$> classParser <*> manyV atomMonotypeParser
    where
      manyV = fmap Vector.fromList . many

data instance ExtensionTypeError X
  = OccurCheckError Tv (Monotype X UniVar)
  | MismatchedTypes (Monotype X UniVar) (Monotype X UniVar)

instance Pretty (ExtensionTypeError X) where
  pretty (OccurCheckError v t) = "occur check failed:" <+> pretty v <+> "~" <+> pretty t
  pretty (MismatchedTypes t1 t2) =
    "could not match expected type"
      <+> squotes (pretty t1)
      <+> "with actual type"
      <+> squotes (pretty t2)

instance Extension X where
  simplifyConstraint given tch initWanted = solve initWantedU initWantedC Subst.empty
    where
      (givenU, givenC) = splitConstraint given
      (initWantedU, initWantedC) = splitConstraint initWanted
      solve wantedU wantedC acc = do
        (residualU1, residualC) <- foldMapM (reduceClassConstraint givenC) wantedC
        (residualU2, unifier) <- reinterpretError $ simplifyUnificationConstraint givenU tch wantedU
        let residualU = substitute unifier residualU1 <> residualU2
        let unifier' = upgradeUnifier unifier
        if Subst.null unifier
          then pure (finalizeConstraint residualU residualC, acc)
          else solve residualU (map (substitute unifier') residualC) (Subst.compose unifier' acc)
      finalizeConstraint u c = toXConstraint u <> foldMap ExtensionConstraint c
      upgradeUnifier (Subst m) = Subst $ fmap U.toXType m
      reinterpretError (Right x) = pure x
      reinterpretError (Left (U.OccurCheckError v t)) =
        throwError . ExtensionTypeError $ OccurCheckError v (U.toXType t)
      reinterpretError (Left (U.MismatchedTypes t1 t2)) =
        throwError . ExtensionTypeError $ MismatchedTypes (U.toXType t1) (U.toXType t2)

type SplitConstraint = (Constraint SimpleUnification UniVar, [ExtensionConstraint X UniVar])

splitConstraint :: Constraint X UniVar -> SplitConstraint
splitConstraint EmptyConstraint = mempty
splitConstraint (ProductConstraint q1 q2) = splitConstraint q1 <> splitConstraint q2
splitConstraint (EqualityConstraint t1 t2) = (EqualityConstraint (toXType t1) (toXType t2), [])
splitConstraint (ExtensionConstraint x) = (EmptyConstraint, [x])

toXType :: Monotype X a -> Monotype x a
toXType (VarType v) = VarType v
toXType (UniType u) = UniType u
toXType (ApplyType k ts) = ApplyType k $ fmap toXType ts

reduceClassConstraint ::
  ( HasProgramEnv X m,
    Fresh m,
    MonadError (TypeError X) m
  ) =>
  [ExtensionConstraint X UniVar] ->
  ExtensionConstraint X UniVar ->
  m SplitConstraint
reduceClassConstraint given q = findInstance q given >>= f
  where
    f Nothing = pure (EmptyConstraint, [q])
    f (Just (uni1, classPreds)) = do
      (uni2, residual) <- foldMapM (reduceClassConstraint given) classPreds
      pure (uni1 <> uni2, residual)

findInstance ::
  ( HasProgramEnv X m,
    Fresh m,
    MonadError (TypeError X) m
  ) =>
  ExtensionConstraint X UniVar ->
  [ExtensionConstraint X UniVar] ->
  m (Maybe SplitConstraint)
findInstance q (h : t)
  | isJust (match h q) = pure $ Just mempty
  | otherwise = findInstance q t
findInstance q [] = getAxiomSchemes >>= go . Vector.toList
  where
    go [] = pure Nothing
    go (ForallAxiomScheme {vars, constraint, head = ExtensionConstraint head} : t) = do
      (constraint', head') <- instantiateClassAxiomScheme vars constraint head
      case match head' q of
        Just u -> pure . Just . splitConstraint $ substitute u constraint'
        Nothing -> go t
    go (_ : t) = go t

match :: ExtensionConstraint X UniVar -> ExtensionConstraint X UniVar -> Maybe (Unifier X)
match (TypeClassConstraint k1 ts1) (TypeClassConstraint k2 ts2)
  | k1 == k2 = matchTypeAll ts1 ts2
  | otherwise = Nothing

matchTypeAll :: Vector (Monotype X UniVar) -> Vector (Monotype X UniVar) -> Maybe (Unifier X)
matchTypeAll ts1 ts2 | Vector.null ts1 && Vector.null ts2 = Just Subst.empty
matchTypeAll (uncons -> Just (h1, t1)) (uncons -> Just (h2, t2)) = do
  u1 <- matchType h1 h2
  u2 <- matchTypeAll t1 t2
  pure $ Subst.compose u1 u2
matchTypeAll _ _ = Nothing

matchType :: Monotype X UniVar -> Monotype X UniVar -> Maybe (Unifier X)
matchType (UniType u) t = Just $ Subst.singleton u t
matchType (VarType v1) (VarType v2) | v1 == v2 = Just Subst.empty
matchType (ApplyType k1 ts1) (ApplyType k2 ts2) | k1 == k2 = matchTypeAll ts1 ts2
matchType _ _ = Nothing

instantiateClassAxiomScheme ::
  ( Fresh m,
    MonadError (TypeError X) m
  ) =>
  Vector TypeVar ->
  Constraint X Void ->
  ExtensionConstraint X Void ->
  m (Constraint X UniVar, ExtensionConstraint X UniVar)
instantiateClassAxiomScheme vars constraint head
  | Just v <- findDuplicate vars = throwError $ ConflictingTypeVars v
  | otherwise = do
    instantiator <- Subst.fromBinders vars
    c <- instantiate (Subst.replace instantiator) constraint
    h <- instantiate (Subst.replace instantiator) head
    pure (c, h)
