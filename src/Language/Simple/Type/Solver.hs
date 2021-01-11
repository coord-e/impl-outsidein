{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Language.Simple.Type.Solver (solveConstraint, ResultingUnifier (..)) where

import Control.Monad (MonadPlus (..), forM, guard, msum, unless)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Logger (MonadLogger)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList, toList)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (member, toList)
import qualified Language.Core.Syntax as Core
import Language.Simple.Fresh (Fresh)
import Language.Simple.Syntax (Monotype (..))
import Language.Simple.Type.Constraint
  ( AtomicConstraint (..),
    GeneratedConstraint (..),
    GivenConstraint (..),
    UniVar,
    fuv,
    implic,
    simple,
  )
import Language.Simple.Type.Env (HasProgramEnv)
import Language.Simple.Type.Error (TypeError (..))
import Language.Simple.Type.Generator (toCoreType)
import Language.Simple.Type.Solver.Canonicalize
  ( CanonicalizeGivenOutput (..),
    CanonicalizeWantedOutput (..),
    canonicalizeGiven,
    canonicalizeWanted,
  )
import Language.Simple.Type.Solver.Evidence
  ( Evidence (..),
    EvidenceStore,
    addEvidence,
    emptyEvidenceStore,
    substituteInEvidenceStore,
    unionEvidenceStore,
  )
import Language.Simple.Type.Solver.Interact (InteractWantedOutput (..), interactGiven, interactWanted)
import Language.Simple.Type.Solver.Simplify (SimplifyOutput (..), simplify)
import Language.Simple.Type.Solver.TopReact
  ( TopReactGivenOutput (..),
    TopReactWantedOutput (..),
    topReactGiven,
    topReactWanted,
  )
import Language.Simple.Type.Substitution (Subst, Substitutable (..), Unifier, substitute)
import qualified Language.Simple.Type.Substitution as Subst (compose, domain, empty, limit, singleton)
import Prettyprinter (Pretty (..), encloseSep, list, tupled, (<+>))
import Util (logParamsDebug)
import Prelude hiding (interact)

data ResultingUnifier = ResultingUnifier
  { simples :: Unifier,
    implications :: HashMap Core.ImplicationId ResultingUnifier
  }

instance Pretty ResultingUnifier where
  pretty ResultingUnifier {simples, implications} = tupled [pretty simples, list . map f $ HashMap.toList implications]
    where
      f (id, u) = pretty id <+> ">" <+> pretty u

solveConstraint ::
  ( HasProgramEnv m,
    Fresh m,
    MonadLogger m,
    MonadError TypeError m
  ) =>
  [GivenConstraint] ->
  HashSet UniVar ->
  GeneratedConstraint ->
  m ([AtomicConstraint], ResultingUnifier, EvidenceStore)
solveConstraint given tch wanted = do
  (residual, unifier, simpleEvidences) <- simplifyConstraint given tch (simple wanted)
  (implics, implicEvidences) <- fmap unzip . forM (implic (substitute unifier wanted)) $ \(id, vars, premise, c) -> do
    (q, u, e) <- solveConstraint (given <> map toGiven residual <> premise) vars c
    unless (null q) $ throwError (UnresolvedConstraint q)
    pure ((id, u), e)
  let evidences = foldr unionEvidenceStore simpleEvidences implicEvidences
  let resultingUnifier = ResultingUnifier {simples = unifier, implications = HashMap.fromList implics}
  logParamsDebug
    "solveConstraint"
    [ ("given", pretty given),
      ("tch", pretty (HashSet.toList tch)),
      ("wanted", pretty wanted),
      ("(out) residual", pretty residual),
      ("(out) unifier", pretty resultingUnifier),
      ("(out) evidences", pretty evidences)
    ]
  pure (residual, resultingUnifier, evidences)
  where
    toGiven (EqualityAtomicConstraint id t1 t2) = EqualityGivenConstraint (Core.UnsolvedCoercion id) t1 t2
    toGiven (TypeClassAtomicConstraint id k ts) = TypeClassGivenConstraint (Core.UnsolvedClassDictionaryExpr id) k ts

simplifyConstraint ::
  ( Fresh m,
    MonadLogger m,
    HasProgramEnv m,
    MonadError TypeError m
  ) =>
  [GivenConstraint] ->
  HashSet UniVar ->
  [AtomicConstraint] ->
  m ([AtomicConstraint], Unifier, EvidenceStore)
simplifyConstraint given tch wanted = do
  Quadruple {tch = tch', flatten, wanted = wanted', evidences} <-
    fixStep $ Quadruple tch Subst.empty given wanted emptyEvidenceStore
  pure . finalize . extract (substituteInEvidenceStore flatten evidences) tch' . fmap (substitute flatten) $ wanted'
  where
    finalize (residual, subst, evidences) = (substitute subst residual, Subst.limit tch subst, substituteInEvidenceStore subst evidences)

extract :: EvidenceStore -> HashSet UniVar -> [AtomicConstraint] -> ([AtomicConstraint], Subst UniVar, EvidenceStore)
extract evidences tch = foldr go ([], Subst.empty, evidences)
  where
    go (EqualityAtomicConstraint id (UniType u) t) (residual, subst, es) | check u t subst = (residual, include u t subst, addEvidence (EqualityEvidence id (Core.ReflCoercion (toCoreType t))) es)
    go (EqualityAtomicConstraint id t (UniType u)) (residual, subst, es) | check u t subst = (residual, include u t subst, addEvidence (EqualityEvidence id (Core.ReflCoercion (toCoreType t))) es)
    go c (residual, subst, es) = (c : residual, subst, es)
    check u t subst = HashSet.member u tch && not (HashSet.member u (fuv t)) && not (HashSet.member u (Subst.domain subst))
    -- TODO: idempotence?
    include u t subst = Subst.compose (Subst.singleton u (substitute subst t)) subst

data Quadruple = Quadruple
  { tch :: HashSet UniVar,
    flatten :: Subst UniVar,
    given :: [GivenConstraint],
    wanted :: [AtomicConstraint],
    evidences :: EvidenceStore
  }

instance Pretty Quadruple where
  pretty Quadruple {tch, flatten, given, wanted, evidences} =
    encloseSep
      "<"
      ">"
      ", "
      [ pretty (HashSet.toList tch),
        pretty flatten,
        pretty given,
        pretty wanted,
        pretty evidences
      ]

fixStep :: (HasProgramEnv m, MonadError TypeError m, MonadLogger m, Fresh m) => Quadruple -> m Quadruple
fixStep quad = f =<< runMaybeT (step quad)
  where
    f Nothing = do
      logParamsDebug
        "step (end)"
        [ ("input", pretty quad)
        ]
      pure quad
    f (Just quad') = do
      logParamsDebug
        "step (changed)"
        [ ("input", pretty quad),
          ("output", pretty quad')
        ]
      fixStep quad'

step :: (HasProgramEnv m, MonadError TypeError m, MonadLogger m, Fresh m) => Quadruple -> MaybeT m Quadruple
step Quadruple {tch, flatten, given, wanted, evidences} =
  all1 cang given
    `mplus` all1 canw wanted
    `mplus` all1 topg given
    `mplus` all1 topw wanted
    `mplus` allPair simpl given wanted
    `mplus` all2 intg given
    `mplus` all2 intw wanted
  where
    cang q1 others = do
      CanonicalizeGivenOutput {tch = tch', flatten = flatten', output} <- canonicalizeGiven q1
      logParamsDebug
        "CANG"
        [ ("Q1", pretty q1),
          ("tch (out)", pretty (HashSet.toList tch')),
          ("flatten (out)", pretty flatten'),
          ("Q2 (out)", pretty output)
        ]
      pure Quadruple {tch = tch <> tch', flatten = Subst.compose flatten' flatten, given = output <> others, wanted, evidences}
    canw q1 others = do
      CanonicalizeWantedOutput {tch = tch', flatten = flatten', output, evidence} <- canonicalizeWanted q1
      logParamsDebug
        "CANW"
        [ ("Q1", pretty q1),
          ("tch (out)", pretty (HashSet.toList tch')),
          ("flatten (out)", pretty flatten'),
          ("Q2 (out)", pretty output),
          ("evidence (out)", pretty evidence)
        ]
      pure Quadruple {tch = tch <> tch', flatten = Subst.compose flatten' flatten, given, wanted = output <> others, evidences = addEvidence evidence evidences}
    intg q1 q2 others = do
      q3 <- interactGiven q1 q2
      logParamsDebug
        "INTG"
        [ ("Q1", pretty q1),
          ("Q2", pretty q2),
          ("Q3 (out)", pretty q3)
        ]
      pure Quadruple {tch, flatten, given = q3 <> others, wanted, evidences}
    intw q1 q2 others = do
      InteractWantedOutput {output = q3, rightEvidence} <- interactWanted q1 q2
      logParamsDebug
        "INTW"
        [ ("Q1", pretty q1),
          ("Q2", pretty q2),
          ("Q3 (out)", pretty q3),
          ("evidence (out)", pretty rightEvidence)
        ]
      pure Quadruple {tch, flatten, given, wanted = q3 <> others, evidences = addEvidence rightEvidence evidences}
    simpl q q1 qg qw = do
      SimplifyOutput {output = q2, evidence} <- simplify q q1
      logParamsDebug
        "SIMPL"
        [ ("Q", pretty q),
          ("Q1", pretty q1),
          ("Q2 (out)", pretty q2),
          ("evidence (out)", pretty evidence)
        ]
      pure Quadruple {tch, flatten, given = q : qg, wanted = q2 <> qw, evidences = addEvidence evidence evidences}
    topg q1 others = do
      TopReactGivenOutput {tch = tch', output} <- topReactGiven q1
      guard (null tch')
      logParamsDebug
        "TOPG"
        [ ("Q1", pretty q1),
          ("Q2 (out)", pretty output)
        ]
      pure Quadruple {tch, flatten, given = output <> others, wanted, evidences}
    topw q1 others = do
      TopReactWantedOutput {tch = tch', output, evidence} <- topReactWanted q1
      logParamsDebug
        "TOPW"
        [ ("Q1", pretty q1),
          ("tch (out)", pretty (HashSet.toList tch')),
          ("Q2 (out)", pretty output),
          ("evidence (out)", pretty evidence)
        ]
      pure Quadruple {tch = tch <> tch', flatten, given, wanted = output <> others, evidences = addEvidence evidence evidences}

all1 :: MonadPlus m => (a -> [a] -> m b) -> [a] -> m b
all1 p xs = go xs []
  where
    go (h : t) acc = p h (t ++ acc) `mplus` go t (h : acc)
    go [] _ = mzero

all1s :: [a] -> [(a, [a])]
all1s = all1 f
  where
    f x xs = pure (x, xs)

all2 :: MonadPlus m => (a -> a -> [a] -> m b) -> [a] -> m b
all2 p xs = msum $ do
  (x, xs') <- all1s xs
  (y, rest) <- all1s xs'
  pure $ p x y rest

allPair :: MonadPlus m => (a -> b -> [a] -> [b] -> m c) -> [a] -> [b] -> m c
allPair p xs ys = msum $ do
  (x, xs') <- all1s xs
  (y, ys') <- all1s ys
  pure $ p x y xs' ys'
