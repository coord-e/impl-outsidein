{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wwarn=orphans #-}

module Language.Simple.Extension.TypeClassTypeFamily.Solver
  (
  )
where

import Control.Monad (MonadPlus (..), guard, msum)
import Control.Monad.Except (MonadError)
import Control.Monad.Logger (MonadLogger)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet (member, toList)
import Language.Simple.Extension (Extension (..))
import Language.Simple.Extension.TypeClassTypeFamily.Canonicalize (CanonicalizeOutput (..), canonicalizeGiven, canonicalizeWanted)
import Language.Simple.Extension.TypeClassTypeFamily.Extension (TypeClassTypeFamily)
import Language.Simple.Extension.TypeClassTypeFamily.Interact (interact)
import Language.Simple.Extension.TypeClassTypeFamily.Simplify (simplify)
import Language.Simple.Extension.TypeClassTypeFamily.Syntax (AtomicConstraint (..), atomicConstraints, fromAtomicConstraint)
import Language.Simple.Extension.TypeClassTypeFamily.TopReact (TopReactOutput (..), topReactGiven, topReactWanted)
import Language.Simple.Fresh (Fresh)
import Language.Simple.Syntax (Constraint (..), Monotype (..))
import Language.Simple.Type.Constraint (UniVar, fuv)
import Language.Simple.Type.Env (HasProgramEnv)
import Language.Simple.Type.Error (TypeError)
import Language.Simple.Type.Substitution (Subst, substitute)
import qualified Language.Simple.Type.Substitution as Subst (compose, domain, empty, limit, singleton)
import Language.Simple.Util (logParamsDebug)
import Prettyprinter (Pretty (..), encloseSep)
import Prelude hiding (interact)

type X = TypeClassTypeFamily

instance Extension X where
  simplifyConstraint given tch wanted = do
    Quadruple {tch = tch', flatten, wanted = wanted'} <-
      fixStep $ Quadruple tch Subst.empty (atomicConstraints given) (atomicConstraints wanted)
    pure . finalize . extract tch' . fmap (substitute flatten) $ wanted'
    where
      finalize (residual, subst) = (substitute subst residual, Subst.limit tch subst)

extract :: HashSet UniVar -> [AtomicConstraint] -> (Constraint X UniVar, Subst X UniVar)
extract tch = foldr go (mempty, Subst.empty)
  where
    go (EqualityAtomicConstraint (UniType u) t) (residual, subst) | check u t subst = (residual, include u t subst)
    go (EqualityAtomicConstraint t (UniType u)) (residual, subst) | check u t subst = (residual, include u t subst)
    go c (residual, subst) = (residual <> fromAtomicConstraint c, subst)
    check u t subst = HashSet.member u tch && not (HashSet.member u (fuv t)) && not (HashSet.member u (Subst.domain subst))
    -- TODO: idempotence?
    include u t subst = Subst.compose (Subst.singleton u (substitute subst t)) subst

data Quadruple = Quadruple
  { tch :: HashSet UniVar,
    flatten :: Subst X UniVar,
    given :: [AtomicConstraint],
    wanted :: [AtomicConstraint]
  }

instance Pretty Quadruple where
  pretty Quadruple {tch, flatten, given, wanted} =
    encloseSep
      "<"
      ">"
      ", "
      [ pretty (HashSet.toList tch),
        pretty flatten,
        pretty given,
        pretty wanted
      ]

fixStep :: (HasProgramEnv X m, MonadError (TypeError X) m, MonadLogger m, Fresh m) => Quadruple -> m Quadruple
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

step :: (HasProgramEnv X m, MonadError (TypeError X) m, MonadLogger m, Fresh m) => Quadruple -> MaybeT m Quadruple
step Quadruple {tch, flatten, given, wanted} =
  all1 cang given
    `mplus` all1 canw wanted
    `mplus` all1 topg given
    `mplus` all1 topw wanted
    `mplus` allPair simpl given wanted
    `mplus` all2 intg given
    `mplus` all2 intw wanted
  where
    cang q1 others = do
      CanonicalizeOutput {tch = tch', flatten = flatten', output} <- canonicalizeGiven q1
      logParamsDebug
        "CANG"
        [ ("Q1", pretty q1),
          ("tch (out)", pretty (HashSet.toList tch')),
          ("flatten (out)", pretty flatten'),
          ("Q2 (out)", pretty output)
        ]
      pure Quadruple {tch = tch <> tch', flatten = Subst.compose flatten' flatten, given = atomicConstraints output <> others, wanted}
    canw q1 others = do
      CanonicalizeOutput {tch = tch', flatten = flatten', output} <- canonicalizeWanted q1
      logParamsDebug
        "CANW"
        [ ("Q1", pretty q1),
          ("tch (out)", pretty (HashSet.toList tch')),
          ("flatten (out)", pretty flatten'),
          ("Q2 (out)", pretty output)
        ]
      pure Quadruple {tch = tch <> tch', flatten = Subst.compose flatten' flatten, given, wanted = atomicConstraints output <> others}
    intg q1 q2 others = do
      q3 <- interact q1 q2
      logParamsDebug
        "INTG"
        [ ("Q1", pretty q1),
          ("Q2", pretty q2),
          ("Q3 (out)", pretty q3)
        ]
      pure Quadruple {tch, flatten, given = atomicConstraints q3 <> others, wanted}
    intw q1 q2 others = do
      q3 <- interact q1 q2
      logParamsDebug
        "INTW"
        [ ("Q1", pretty q1),
          ("Q2", pretty q2),
          ("Q3 (out)", pretty q3)
        ]
      pure Quadruple {tch, flatten, given, wanted = atomicConstraints q3 <> others}
    simpl q q1 qg qw = do
      q2 <- simplify q q1
      logParamsDebug
        "SIMPL"
        [ ("Q", pretty q),
          ("Q1", pretty q1),
          ("Q2 (out)", pretty q2)
        ]
      pure Quadruple {tch, flatten, given = q : qg, wanted = atomicConstraints q2 <> qw}
    topg q1 others = do
      TopReactOutput {tch = tch', output} <- topReactGiven q1
      guard (null tch')
      logParamsDebug
        "TOPG"
        [ ("Q1", pretty q1),
          ("Q2 (out)", pretty output)
        ]
      pure Quadruple {tch, flatten, given = atomicConstraints output <> others, wanted}
    topw q1 others = do
      TopReactOutput {tch = tch', output} <- topReactWanted q1
      logParamsDebug
        "TOPG"
        [ ("Q1", pretty q1),
          ("tch (out)", pretty (HashSet.toList tch')),
          ("Q2 (out)", pretty output)
        ]
      pure Quadruple {tch = tch <> tch', flatten, given, wanted = atomicConstraints output <> others}

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
