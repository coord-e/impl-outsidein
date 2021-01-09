{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Core.Syntax
  ( Program (..),
    Binding (..),
    CompleteType,
    CompleteTermVarBinder,
    CompleteExpr,
    takePropositionLhs,
    takePropositionRhs,
    CompleteProposition,
    CompleteCaseArm,
    CompleteCoercion,
    CompleteCoercionVarBinder,
    AxiomName (..),
    AxiomScheme (..),
    DataCtorType (..),
    Expr (..),
    TermVarBinder (..),
    CoercionVarBinder (..),
    CaseArm (..),
    Type (..),
    pattern FunctionType,
    Coercion (..),
    Proposition (..),
    DataCtor (..),
    TermVar (..),
    TypeVar (..),
    Class (..),
    Family (..),
    TypeCtor (..),
    CoercionVar (..),
  )
where

import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, null, toList)
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Simple.Syntax
  ( Class (..),
    DataCtor (..),
    Family (..),
    TermVar (..),
    TypeVar (..),
  )
import Prettyprinter (Doc, Pretty (..), encloseSep, hsep, parens, (<+>))
import Prettyprinter.Internal (unsafeTextWithoutNewlines)

data Program = Program
  { bindings :: Vector Binding,
    axioms :: HashMap AxiomName AxiomScheme,
    vars :: HashMap TermVar CompleteType,
    dataCtors :: HashMap DataCtor DataCtorType
  }
  deriving (Generic, Show, Eq)

data Binding = Binding CompleteTermVarBinder CompleteExpr
  deriving (Generic, Show, Eq)

instance Pretty Binding where
  pretty (Binding b e) = pretty b <+> "=" <+> pretty e

data AxiomScheme = ForallAxiomScheme
  { vars :: Vector TypeVar,
    lhs :: CompleteType,
    rhs :: CompleteType
  }
  deriving (Generic, Show, Eq)

instance Pretty AxiomScheme where
  pretty ForallAxiomScheme {vars, lhs, rhs} =
    hsep
      [ "∀" <> hsep (map pretty $ Vector.toList vars) <> ".",
        pretty lhs <+> "~" <+> pretty rhs
      ]

data DataCtorType = DataCtorType
  { universalVars :: Vector TypeVar,
    existentialVars :: Vector TypeVar,
    coercionVars :: Vector CompleteProposition,
    fields :: Vector CompleteType,
    ctor :: TypeCtor,
    ctorArgs :: Vector TypeVar
  }
  deriving (Generic, Show, Eq)

instance Pretty DataCtorType where
  pretty DataCtorType {universalVars, existentialVars, coercionVars, fields, ctor, ctorArgs} =
    hsep
      [ "∀" <> hsep (map pretty $ Vector.toList universalVars) <> ".",
        "∃" <> hsep (map pretty $ Vector.toList existentialVars) <> ".",
        "∃" <> hsep (map (parens . pretty) $ Vector.toList coercionVars) <> ".",
        hsep (map ((<> "→") . pretty) $ Vector.toList fields),
        pretty ctor <+> hsep (map pretty $ Vector.toList ctorArgs)
      ]

data Expr a c d
  = UnsolvedClassDictionaryExpr d
  | CtorExpr DataCtor
  | VarExpr TermVar
  | LambdaExpr (TermVarBinder a) (Expr a c d)
  | TypeLambdaExpr TypeVar (Expr a c d)
  | CoercionLambdaExpr (CoercionVarBinder a) (Expr a c d)
  | ApplyExpr (Expr a c d) (Expr a c d)
  | TypeApplyExpr (Expr a c d) (Type a)
  | CoercionApplyExpr (Expr a c d) (Coercion a c)
  | CaseExpr (Expr a c d) (Type a) (Vector (CaseArm a c d))
  | LetExpr (TermVarBinder a) (Expr a c d) (Expr a c d)
  | CastExpr (Expr a c d) (Coercion a c)
  deriving (Generic, Show, Eq)

type CompleteExpr = Expr Void Void Void

instance (Pretty a, Pretty c, Pretty d) => Pretty (Expr a c d) where
  pretty (UnsolvedClassDictionaryExpr d) = pretty d
  pretty (CtorExpr k) = pretty k
  pretty (VarExpr x) = pretty x
  pretty (LambdaExpr b e) = "λ" <> pretty b <> "." <+> pretty e
  pretty (TypeLambdaExpr v e) = "Λ" <> pretty v <> "." <+> pretty e
  pretty (CoercionLambdaExpr b e) = "Λ" <> parens (pretty b) <> "." <+> pretty e
  pretty (ApplyExpr e1 e2) = prettyAtomExpr e1 <+> prettyAtomExpr e2
  pretty (TypeApplyExpr e t) = pretty e <+> "@" <> prettyAtomType t
  pretty (CoercionApplyExpr e c) = pretty e <+> "@" <> prettyAtomCoercion c
  pretty (CaseExpr e t arms) =
    "case" <+> pretty e <+> "return"
      <+> pretty t
      <+> encloseSep "{" "}" ", " (map pretty $ Vector.toList arms)
  pretty (LetExpr b e1 e2) = "let" <+> pretty b <+> "=" <+> pretty e1 <+> "in" <+> pretty e2
  pretty (CastExpr e c) = pretty e <+> "▹" <+> pretty c

prettyAtomExpr :: (Pretty a, Pretty c, Pretty d) => Expr a c d -> Doc ann
prettyAtomExpr e@ApplyExpr {} = parens (pretty e)
prettyAtomExpr e@TypeApplyExpr {} = parens (pretty e)
prettyAtomExpr e@CoercionApplyExpr {} = parens (pretty e)
prettyAtomExpr e@CastExpr {} = parens (pretty e)
prettyAtomExpr e = pretty e

data CaseArm a c d = CaseArm
  { ctor :: DataCtor,
    typeArgs :: Vector (Type a),
    existentialVars :: Vector TypeVar,
    coercionVars :: Vector (CoercionVarBinder a),
    termVars :: Vector (TermVarBinder a),
    body :: Expr a c d
  }
  deriving (Generic, Show, Eq)

type CompleteCaseArm = CaseArm Void Void Void

instance (Pretty a, Pretty c, Pretty d) => Pretty (CaseArm a c d) where
  pretty CaseArm {ctor, typeArgs, existentialVars, coercionVars, termVars, body} =
    hsep
      [ pretty ctor,
        hsep (map (("@" <>) . prettyAtomType) $ Vector.toList typeArgs),
        hsep (map ((">" <>) . pretty) $ Vector.toList existentialVars),
        hsep (map ((">" <>) . parens . pretty) $ Vector.toList coercionVars),
        hsep (map (parens . pretty) $ Vector.toList termVars),
        "=>",
        pretty body
      ]

data TermVarBinder a = TermVarBinder TermVar (Type a)
  deriving (Generic, Show, Eq)

type CompleteTermVarBinder = TermVarBinder Void

instance Pretty a => Pretty (TermVarBinder a) where
  pretty (TermVarBinder v t) = pretty v <+> "::" <+> pretty t

data CoercionVarBinder a = CoercionVarBinder CoercionVar (Proposition a)
  deriving (Generic, Show, Eq)

type CompleteCoercionVarBinder = CoercionVarBinder Void

instance Pretty a => Pretty (CoercionVarBinder a) where
  pretty (CoercionVarBinder v p) = pretty v <+> "::" <+> pretty p

data TypeCtor
  = NamedTypeCtor Text
  | ClassDictionaryTypeCtor Class
  | FunctionTypeCtor
  deriving stock (Show, Ord, Eq, Generic)
  deriving anyclass (Hashable)

instance Pretty TypeCtor where
  pretty (NamedTypeCtor k) = unsafeTextWithoutNewlines k
  pretty (ClassDictionaryTypeCtor k) = "{" <> pretty k <> "}"
  pretty FunctionTypeCtor = "(->)"

data Type a
  = UniType a
  | VarType TypeVar
  | ApplyType TypeCtor (Vector (Type a))
  | FamilyApplyType Family (Vector (Type a))
  | ForallType TypeVar (Type a)
  | CoercionForallType (Proposition a) (Type a)
  deriving (Generic, Show, Eq)

type CompleteType = Type Void

pattern FunctionType :: Type a -> Type a -> Type a
pattern FunctionType a b <-
  ApplyType FunctionTypeCtor (Vector.toList -> [a, b])
  where
    FunctionType a b = ApplyType FunctionTypeCtor $ Vector.fromList [a, b]

instance Pretty a => Pretty (Type a) where
  pretty (UniType a) = pretty a
  pretty (VarType v) = pretty v
  pretty (FunctionType t1 t2)
    | isNested t1 = parens (pretty t1) <+> "->" <+> pretty t2
    | otherwise = pretty t1 <+> "->" <+> pretty t2
    where
      isNested (FunctionType _ _) = True
      isNested _ = False
  pretty (ApplyType k ts) = hsep (pretty k : map prettyAtomType (Vector.toList ts))
  pretty (FamilyApplyType k ts) = "<" <> hsep (pretty k : map prettyAtomType (Vector.toList ts)) <> ">"
  pretty (ForallType v t) = "∀" <> pretty v <> "." <+> pretty t
  pretty (CoercionForallType p t) = "∀" <> parens (pretty p) <> "." <+> pretty t

prettyAtomType :: Pretty a => Type a -> Doc ann
prettyAtomType v@UniType {} = pretty v
prettyAtomType v@VarType {} = pretty v
prettyAtomType v@FamilyApplyType {} = pretty v
prettyAtomType v@(ApplyType _ ts) | Vector.null ts = pretty v
prettyAtomType v = parens (pretty v)

newtype AxiomName = AxiomName Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty AxiomName where
  pretty (AxiomName n) = "$" <> unsafeTextWithoutNewlines n

newtype CoercionVar = CoercionVar Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty CoercionVar where
  pretty (CoercionVar v) = unsafeTextWithoutNewlines v

data Proposition a = Proposition (Type a) (Type a)
  deriving (Generic, Show, Eq)

type CompleteProposition = Proposition Void

takePropositionLhs, takePropositionRhs :: Proposition a -> Type a
takePropositionLhs (Proposition lhs _) = lhs
takePropositionRhs (Proposition _ rhs) = rhs

instance Pretty a => Pretty (Proposition a) where
  pretty (Proposition t1 t2) = pretty t1 <+> "~" <+> pretty t2

data Coercion a c
  = UnsolvedCoercion c
  | AxiomCoercion AxiomName (Vector (Type a))
  | VarCoercion CoercionVar
  | TypeCtorCoercion TypeCtor (Vector (Coercion a c))
  | FamilyCoercion Family (Vector (Coercion a c))
  | ReflCoercion (Type a)
  | TransCoercion (Coercion a c) (Coercion a c)
  | SymmCoercion (Coercion a c)
  | EquivalentCoercion (Coercion a c) (Coercion a c)
  deriving (Generic, Show, Eq)

type CompleteCoercion = Coercion Void Void

instance (Pretty a, Pretty c) => Pretty (Coercion a c) where
  pretty (UnsolvedCoercion c) = pretty c
  pretty (AxiomCoercion n tys) = hsep (pretty n : map (("@" <>) . prettyAtomType) (Vector.toList tys))
  pretty (VarCoercion v) = pretty v
  pretty (TypeCtorCoercion k cs) = hsep (pretty k : map prettyAtomCoercion (Vector.toList cs))
  pretty (FamilyCoercion k cs) = "<" <> hsep (pretty k : map prettyAtomCoercion (Vector.toList cs)) <> ">"
  pretty (ReflCoercion t) = "<" <> pretty t <> ">"
  pretty (TransCoercion c1 c2) = prettyAtomCoercion c1 <+> "∘" <+> prettyAtomCoercion c2
  pretty (SymmCoercion c) = "sym" <+> prettyAtomCoercion c
  pretty (EquivalentCoercion c1 c2) = prettyAtomCoercion c1 <+> ", " <+> prettyAtomCoercion c2

prettyAtomCoercion :: (Pretty a, Pretty c) => Coercion a c -> Doc ann
prettyAtomCoercion c@UnsolvedCoercion {} = pretty c
prettyAtomCoercion c@VarCoercion {} = pretty c
prettyAtomCoercion c@FamilyCoercion {} = pretty c
prettyAtomCoercion c@ReflCoercion {} = pretty c
prettyAtomCoercion c = parens (pretty c)
