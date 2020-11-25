{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Simple.Extension.TypeClassTypeFamily.TopReact
  ( topReactGiven,
    topReactWanted,
    TopReactOutput (..),
  )
where

import Control.Monad (MonadPlus (..), forM_)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Foldable (foldlM)
import qualified Data.HashMap.Strict as HashMap (elems, union)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (member, singleton)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (filter, zip)
import Data.Void (Void, vacuous)
import Language.Simple.Extension (instantiate)
import Language.Simple.Extension.TypeClassTypeFamily.Extension (ExtensionTypeError (..), TypeClassTypeFamily)
import Language.Simple.Extension.TypeClassTypeFamily.Syntax
  ( AtomicConstraint (..),
    ClassConstraint (..),
    ConstraintLocation (..),
    FamilyType (..),
    fromAtomicConstraint,
    pattern FamilyApplyType,
    pattern FamilyFree,
    pattern FamilyFreeSeq,
    pattern TypeClassConstraint,
  )
import Language.Simple.Fresh (Fresh)
import Language.Simple.Syntax (AxiomScheme (..), Constraint (..), Monotype (..), TypeVar)
import Language.Simple.Type.Constraint (UniVar, fuv)
import Language.Simple.Type.Env (HasProgramEnv (..))
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Substitution (Instantiator, Subst (..), substitute)
import qualified Language.Simple.Type.Substitution as Subst (compose, empty, fromBinders, replace, singleton)
import Language.Simple.Util (findDuplicate, firstJust)
import Prelude hiding (head)

type X = TypeClassTypeFamily

data TopReactOutput = TopReactOutput
  { tch :: HashSet UniVar,
    output :: Constraint X UniVar
  }

topReactGiven :: (HasProgramEnv X m, Fresh m, MonadError (TypeError X) m) => AtomicConstraint -> MaybeT m TopReactOutput
topReactGiven q = topReactFamily Given q `mplus` topReactClass Given q

topReactWanted :: (HasProgramEnv X m, Fresh m, MonadError (TypeError X) m) => AtomicConstraint -> MaybeT m TopReactOutput
topReactWanted q = topReactFamily Wanted q `mplus` topReactClass Wanted q

topReactClass ::
  ( HasProgramEnv X m,
    MonadError (TypeError X) m,
    Fresh m
  ) =>
  ConstraintLocation ->
  AtomicConstraint ->
  MaybeT m TopReactOutput
topReactClass l q@(ClassAtomicConstraint k (FamilyFreeSeq ts)) = do
  MatchingClassAxiom {onlyPredicateVars, predicate, subst = Subst subst} <- findMatchingClassAxiom (ClassConstraint k ts)
  case l of
    Given -> throwError . ExtensionTypeError $ MatchingGivenConstraint (fromAtomicConstraint q)
    Wanted -> do
      Subst onlyPredicateSubst <- Subst.fromBinders onlyPredicateVars
      -- TODO: deal with raw subst manipulation
      let instantiator = Subst $ HashMap.union subst onlyPredicateSubst
      output <- instantiate (Subst.replace instantiator) predicate
      let tch = foldMap fuv $ HashMap.elems onlyPredicateSubst
      pure TopReactOutput {tch, output}
topReactClass _ _ = mzero

topReactFamily ::
  ( HasProgramEnv X m,
    MonadError (TypeError X) m,
    Fresh m
  ) =>
  ConstraintLocation ->
  AtomicConstraint ->
  MaybeT m TopReactOutput
topReactFamily l (EqualityAtomicConstraint (FamilyApplyType k (FamilyFreeSeq ts)) (FamilyFree t)) = do
  MatchingFamilyAxiom {onlyRhsVars, rhs, subst = Subst subst} <- findMatchingFamilyAxiom (FamilyType k ts)
  Subst onlyRhsSubst <- Subst.fromBinders onlyRhsVars
  -- TODO: deal with raw subst manipulation
  let instantiator = Subst $ HashMap.union subst onlyRhsSubst
  rhs' <- instantiate (Subst.replace instantiator) rhs
  pure TopReactOutput {tch = tchOf l onlyRhsSubst, output = EqualityConstraint rhs' t}
  where
    tchOf Wanted = foldMap fuv . HashMap.elems
    tchOf Given = const mempty
topReactFamily _ _ = mzero

data MatchingClassAxiom = MatchingClassAxiom
  { onlyPredicateVars :: Vector TypeVar,
    predicate :: Constraint X Void,
    subst :: Instantiator X
  }

findMatchingClassAxiom ::
  ( HasProgramEnv X m,
    MonadError (TypeError X) m
  ) =>
  ClassConstraint UniVar ->
  MaybeT m MatchingClassAxiom
findMatchingClassAxiom cls = do
  schemes <- lift getAxiomSchemes
  (vars, ts0, predicate, subst) <- MaybeT . pure $ firstJust go schemes
  forM_ (findDuplicate vars) $ throwError . ConflictingTypeVars
  let onlyPredicateVars = Vector.filter (not . (`HashSet.member` foldMap frv ts0)) vars
  pure MatchingClassAxiom {onlyPredicateVars, predicate, subst}
  where
    go ForallAxiomScheme {vars, constraint, head = TypeClassConstraint k0 (FamilyFreeSeq ts0)}
      | Just subst <- matchClass (ClassConstraint k0 ts0) cls =
        Just (vars, ts0, constraint, subst)
    go ForallAxiomScheme {} = Nothing

data MatchingFamilyAxiom = MatchingFamilyAxiom
  { onlyRhsVars :: Vector TypeVar,
    rhs :: Monotype X Void,
    subst :: Instantiator X
  }

findMatchingFamilyAxiom ::
  ( HasProgramEnv X m,
    MonadError (TypeError X) m
  ) =>
  FamilyType UniVar ->
  MaybeT m MatchingFamilyAxiom
findMatchingFamilyAxiom fam = do
  schemes <- lift getAxiomSchemes
  (vars, ts0, rhs, subst) <- MaybeT . pure $ firstJust go schemes
  forM_ (findDuplicate vars) $ throwError . ConflictingTypeVars
  let onlyRhsVars = Vector.filter (not . (`HashSet.member` foldMap frv ts0)) vars
  pure MatchingFamilyAxiom {onlyRhsVars, rhs, subst}
  where
    go
      ForallAxiomScheme
        { vars,
          constraint = EmptyConstraint,
          head = EqualityConstraint (FamilyApplyType k0 (FamilyFreeSeq ts0)) rhs
        }
        | Just subst <- matchFamily (FamilyType k0 ts0) fam =
          Just (vars, ts0, rhs, subst)
    go ForallAxiomScheme {} = Nothing

frv :: Monotype X Void -> HashSet TypeVar
frv (VarType v) = HashSet.singleton v
frv (ApplyType _ ts) = foldMap frv ts
frv (FamilyApplyType _ ts) = foldMap frv ts

matchClass :: ClassConstraint Void -> ClassConstraint UniVar -> Maybe (Instantiator X)
matchClass (ClassConstraint k1 ts1) (ClassConstraint k2 ts2)
  | k1 == k2 = matchTypes (fmap vacuous ts1) ts2
  | otherwise = Nothing

matchFamily :: FamilyType Void -> FamilyType UniVar -> Maybe (Instantiator X)
matchFamily (FamilyType k1 ts1) (FamilyType k2 ts2)
  | k1 == k2 = matchTypes (fmap vacuous ts1) ts2
  | otherwise = Nothing

matchType :: Monotype X UniVar -> Monotype X UniVar -> Maybe (Instantiator X)
matchType (VarType v1) (VarType v2) | v1 == v2 = Just Subst.empty
matchType (VarType v) t = Just $ Subst.singleton v t
matchType (ApplyType k1 ts1) (ApplyType k2 ts2) | k1 == k2 = matchTypes ts1 ts2
matchType _ _ = Nothing

matchTypes :: Vector (Monotype X UniVar) -> Vector (Monotype X UniVar) -> Maybe (Instantiator X)
matchTypes ts1 ts2
  | length ts1 == length ts2 = foldlM go Subst.empty $ Vector.zip ts1 ts2
  | otherwise = Nothing
  where
    go acc (t1, t2) = do
      s <- matchType (substitute acc t1) (substitute acc t2)
      pure $ Subst.compose s acc
