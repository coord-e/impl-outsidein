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

module Language.Simple.ConstraintDomain.TypeClass
  ( TypeClass,
    Class (..),
  )
where

import Control.Applicative (empty, many)
import Control.Monad (forM_)
import Control.Monad.Except (MonadError (..))
import Data.Hashable (Hashable)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, toList)
import Data.Void (vacuous)
import GHC.Generics (Generic)
import Language.Simple.ConstraintDomain
  ( ConstraintDomain (..),
    ExtensionConstraint,
    ExtensionMonotype,
    ExtensionTypeError,
    Generalizable (..),
    Instantiable (..),
    SyntaxExtension (..),
  )
import Language.Simple.ConstraintDomain.SimpleUnification
  ( SimpleUnification,
    simplifyUnificationConstraint,
    toXConstraint,
  )
import qualified Language.Simple.ConstraintDomain.SimpleUnification as U (ExtensionTypeError (..), toXType)
import Language.Simple.ConstraintDomain.Util (Ftv (..), Tv, matchTypes)
import Language.Simple.Fresh (Fresh (..))
import Language.Simple.Parser (atomMonotypeParser, upperName)
import Language.Simple.Syntax (AxiomScheme (..), Constraint (..), Monotype (..), prettyAtomMonotype)
import Language.Simple.Type.Constraint (Fuv (..), UniVar)
import Language.Simple.Type.Env (HasProgramEnv (..))
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Subst (..), Substitutable (..))
import qualified Language.Simple.Type.Substitution as Subst (compose, empty, null)
import Prettyprinter (Pretty (..), hsep, squotes, (<+>))
import Prettyprinter.Internal (unsafeTextWithoutNewlines)
import Text.Parser.Token (TokenParsing)
import Util (findDuplicate, foldMapM)
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

instance Ftv (ExtensionMonotype X a) where
  ftv = discardMonotypeExt

instance Pretty (ExtensionMonotype X a) where
  pretty = discardMonotypeExt

instance Generalizable X (ExtensionMonotype X) where
  generalize _ = discardMonotypeExt

instance Instantiable X (ExtensionMonotype X) where
  instantiate _ = discardMonotypeExt

instance Substitutable X UniVar (ExtensionMonotype X a) where
  substitute _ = discardMonotypeExt

instance Substitutable X Tv (ExtensionMonotype X a) where
  substitute _ = discardMonotypeExt

instance SyntaxExtension X (ExtensionMonotype X) where
  extensionParser = empty

data instance ExtensionConstraint X a
  = TypeClassConstraint Class (Vector (Monotype X a))

instance Functor (ExtensionConstraint X) where
  fmap f (TypeClassConstraint k ts) = TypeClassConstraint k $ fmap (fmap f) ts

instance Fuv (ExtensionConstraint X UniVar) where
  fuv (TypeClassConstraint _ ts) = foldMap fuv ts

instance Ftv (ExtensionConstraint X UniVar) where
  ftv (TypeClassConstraint _ ts) = foldMap ftv ts

instance Pretty a => Pretty (ExtensionConstraint X a) where
  pretty (TypeClassConstraint k ts) = hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))

instance Generalizable X (ExtensionConstraint X) where
  generalize f (TypeClassConstraint k ts) = TypeClassConstraint k <$> traverse (generalize f) ts

instance Instantiable X (ExtensionConstraint X) where
  instantiate f (TypeClassConstraint k ts) = TypeClassConstraint k <$> traverse (instantiate f) ts

instance Substitutable X UniVar (ExtensionConstraint X UniVar) where
  substitute s (TypeClassConstraint k ts) = TypeClassConstraint k $ fmap (substitute s) ts

instance Substitutable X Tv (ExtensionConstraint X UniVar) where
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

instance ConstraintDomain X where
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
  | isJust (matchClass h q) = pure $ Just mempty
  | otherwise = findInstance q t
findInstance q [] = getAxiomSchemes >>= go . Vector.toList
  where
    go [] = pure Nothing
    go (ForallAxiomScheme {vars, constraint, head = ExtensionConstraint head} : _)
      | Just subst <- matchClass (vacuous head) q = do
        forM_ (findDuplicate vars) $ throwError . ConflictingTypeVars
        let constraint' = substitute subst (vacuous constraint)
        pure . Just $ splitConstraint constraint'
    go (_ : t) = go t

matchClass :: ExtensionConstraint X UniVar -> ExtensionConstraint X UniVar -> Maybe (Subst X Tv)
matchClass (TypeClassConstraint k1 ts1) (TypeClassConstraint k2 ts2)
  | k1 == k2 = matchTypes ts1 ts2
  | otherwise = Nothing
