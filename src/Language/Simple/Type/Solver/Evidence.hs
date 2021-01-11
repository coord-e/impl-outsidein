{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Simple.Type.Solver.Evidence
  ( Evidence (..),
    makeAxiomName,
    makeDictionaryVar,
    unionEvidenceStore,
    EvidenceStore (..),
    addEvidence,
    emptyEvidenceStore,
    substituteInEvidenceStore,
  )
where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
  ( empty,
    insert,
    intersection,
    lookup,
    lookupDefault,
    map,
    null,
    toList,
    union,
  )
import Data.Text (pack)
import GHC.Generics (Generic)
import Language.Core.Syntax (AxiomName (..), TermVar (..))
import qualified Language.Core.Syntax as Core
import Language.Simple.Syntax (Monotype (..))
import Language.Simple.Type.Constraint
  ( AxiomSchemeId (..),
    DictionaryId,
    EqualityId,
    GeneratedCoreCoercion,
    GeneratedCoreExpr,
    GeneratedCoreType,
    UniVar,
  )
import Language.Simple.Type.Generator (toCoreType)
import Language.Simple.Type.Substitution (Subst (..))
import Prettyprinter (Pretty (..), list, (<+>))

data Evidence
  = EqualityEvidence EqualityId GeneratedCoreCoercion
  | DictionaryEvidence DictionaryId GeneratedCoreExpr
  deriving (Generic, Show, Eq)

instance Pretty Evidence where
  pretty (EqualityEvidence id c) = pretty id <> ":" <+> pretty c
  pretty (DictionaryEvidence id d) = pretty id <> ":" <+> pretty d

makeAxiomName :: AxiomSchemeId -> AxiomName
makeAxiomName (AxiomSchemeId n) = AxiomName ("a" <> pack (show n))

makeDictionaryVar :: AxiomSchemeId -> TermVar
makeDictionaryVar (AxiomSchemeId n) = TermVar ("$d" <> pack (show n))

data EvidenceStore = EvidenceStore
  { equality :: HashMap EqualityId GeneratedCoreCoercion,
    dictionary :: HashMap DictionaryId GeneratedCoreExpr
  }
  deriving (Generic, Show, Eq)

instance Pretty EvidenceStore where
  pretty = list . map pretty . evidences

evidences :: EvidenceStore -> [Evidence]
evidences EvidenceStore {equality, dictionary} = unzipWith EqualityEvidence equality <> unzipWith DictionaryEvidence dictionary
  where
    unzipWith p = map (uncurry p) . HashMap.toList

addEvidence :: Evidence -> EvidenceStore -> EvidenceStore
addEvidence (EqualityEvidence id c) s@EvidenceStore {equality} =
  case HashMap.lookup id equality of
    Just _ -> error "addEvidence: duplicated equality id"
    Nothing -> s {equality = HashMap.insert id c equality}
addEvidence (DictionaryEvidence id d) s@EvidenceStore {dictionary} =
  case HashMap.lookup id dictionary of
    Just _ -> error "addEvidence: duplicated dictionary id"
    Nothing -> s {dictionary = HashMap.insert id d dictionary}

emptyEvidenceStore :: EvidenceStore
emptyEvidenceStore = EvidenceStore HashMap.empty HashMap.empty

unionEvidenceStore :: EvidenceStore -> EvidenceStore -> EvidenceStore
unionEvidenceStore s1 s2
  | not (disjoint (equality s1) (equality s2)) = error "unionEvidenceStore: duplicated equality id"
  | not (disjoint (dictionary s1) (dictionary s2)) = error "unionEvidenceStore: duplicated dictionary id"
  | otherwise = EvidenceStore {equality = HashMap.union (equality s1) (equality s2), dictionary = HashMap.union (dictionary s1) (dictionary s2)}
  where
    disjoint m1 m2 = HashMap.null (HashMap.intersection m1 m2)

substituteInEvidenceStore :: Subst UniVar -> EvidenceStore -> EvidenceStore
substituteInEvidenceStore s EvidenceStore {equality, dictionary} =
  EvidenceStore
    { equality = HashMap.map (substituteCoercion s) equality,
      dictionary = HashMap.map (substituteEvidenceExpr s) dictionary
    }

substituteType :: Subst UniVar -> GeneratedCoreType -> GeneratedCoreType
substituteType (Subst m) (Core.UniType u) = toCoreType (HashMap.lookupDefault (UniType u) u m)
substituteType _ (Core.VarType v) = Core.VarType v
substituteType s (Core.ApplyType k ts) = Core.ApplyType k (fmap (substituteType s) ts)
substituteType s (Core.FamilyApplyType k ts) = Core.FamilyApplyType k (fmap (substituteType s) ts)
substituteType s (Core.ForallType v t) = Core.ForallType v (substituteType s t)
substituteType s (Core.CoercionForallType p t) = Core.CoercionForallType p (substituteType s t)

substituteCoercion :: Subst UniVar -> GeneratedCoreCoercion -> GeneratedCoreCoercion
substituteCoercion _ (Core.UnsolvedCoercion c) = Core.UnsolvedCoercion c
substituteCoercion s (Core.AxiomCoercion n ts) = Core.AxiomCoercion n (fmap (substituteType s) ts)
substituteCoercion _ (Core.VarCoercion v) = Core.VarCoercion v
substituteCoercion s (Core.TypeCtorCoercion k cs) = Core.TypeCtorCoercion k (fmap (substituteCoercion s) cs)
substituteCoercion s (Core.FamilyCoercion k cs) = Core.FamilyCoercion k (fmap (substituteCoercion s) cs)
substituteCoercion s (Core.RightCoercion n c) = Core.RightCoercion n (substituteCoercion s c)
substituteCoercion s (Core.ReflCoercion t) = Core.ReflCoercion (substituteType s t)
substituteCoercion s (Core.TransCoercion c1 c2) = Core.TransCoercion (substituteCoercion s c1) (substituteCoercion s c2)
substituteCoercion s (Core.SymmCoercion c) = Core.SymmCoercion (substituteCoercion s c)
substituteCoercion s (Core.EquivalentCoercion c1 c2) = Core.EquivalentCoercion (substituteCoercion s c1) (substituteCoercion s c2)

substituteEvidenceExpr :: Subst UniVar -> GeneratedCoreExpr -> GeneratedCoreExpr
substituteEvidenceExpr _ (Core.UnsolvedClassDictionaryExpr d) = Core.UnsolvedClassDictionaryExpr d
substituteEvidenceExpr _ (Core.CtorExpr k) = Core.CtorExpr k
substituteEvidenceExpr _ (Core.VarExpr x) = Core.VarExpr x
substituteEvidenceExpr s (Core.ApplyExpr e1 e2) = Core.ApplyExpr (substituteEvidenceExpr s e1) (substituteEvidenceExpr s e2)
substituteEvidenceExpr s (Core.TypeApplyExpr e t) = Core.TypeApplyExpr (substituteEvidenceExpr s e) (substituteType s t)
substituteEvidenceExpr s (Core.CoercionApplyExpr e c) = Core.CoercionApplyExpr (substituteEvidenceExpr s e) (substituteCoercion s c)
substituteEvidenceExpr _ e = e
