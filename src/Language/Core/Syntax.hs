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
    vars :: HashMap TermVar Type,
    dataCtors :: HashMap DataCtor DataCtorType
  }
  deriving (Generic, Show, Eq)

data Binding = Binding TermVarBinder Expr
  deriving (Generic, Show, Eq)

instance Pretty Binding where
  pretty (Binding b e) = pretty b <+> "=" <+> pretty e

data AxiomScheme = ForallAxiomScheme
  { vars :: Vector TypeVar,
    lhs :: Type,
    rhs :: Type
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
    coercionVars :: Vector Proposition,
    fields :: Vector Type,
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

data Expr
  = CtorExpr DataCtor
  | VarExpr TermVar
  | LambdaExpr TermVarBinder Expr
  | TypeLambdaExpr TypeVar Expr
  | CoercionLambdaExpr CoercionVarBinder Expr
  | ApplyExpr Expr Expr
  | TypeApplyExpr Expr Type
  | CoercionApplyExpr Expr Coercion
  | CaseExpr Expr Type (Vector CaseArm)
  | LetExpr TermVarBinder Expr Expr
  | CastExpr Expr Coercion
  deriving (Generic, Show, Eq)

instance Pretty Expr where
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

prettyAtomExpr :: Expr -> Doc ann
prettyAtomExpr e@ApplyExpr {} = parens (pretty e)
prettyAtomExpr e@TypeApplyExpr {} = parens (pretty e)
prettyAtomExpr e@CoercionApplyExpr {} = parens (pretty e)
prettyAtomExpr e@CastExpr {} = parens (pretty e)
prettyAtomExpr e = pretty e

data CaseArm = CaseArm
  { ctor :: DataCtor,
    typeArgs :: Vector Type,
    existentialVars :: Vector TypeVar,
    coercionVars :: Vector CoercionVarBinder,
    termVars :: Vector TermVarBinder,
    body :: Expr
  }
  deriving (Generic, Show, Eq)

instance Pretty CaseArm where
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

data TermVarBinder = TermVarBinder TermVar Type
  deriving (Generic, Show, Eq)

instance Pretty TermVarBinder where
  pretty (TermVarBinder v t) = pretty v <+> "::" <+> pretty t

data CoercionVarBinder = CoercionVarBinder CoercionVar Proposition
  deriving (Generic, Show, Eq)

instance Pretty CoercionVarBinder where
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

data Type
  = VarType TypeVar
  | ApplyType TypeCtor (Vector Type)
  | FamilyApplyType Family (Vector Type)
  | ForallType TypeVar Type
  | CoercionForallType Proposition Type
  deriving (Generic, Show, Eq)

pattern FunctionType :: Type -> Type -> Type
pattern FunctionType a b <-
  ApplyType FunctionTypeCtor (Vector.toList -> [a, b])
  where
    FunctionType a b = ApplyType FunctionTypeCtor $ Vector.fromList [a, b]

instance Pretty Type where
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

prettyAtomType :: Type -> Doc ann
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

data Proposition = Proposition Type Type
  deriving (Generic, Show, Eq)

instance Pretty Proposition where
  pretty (Proposition t1 t2) = pretty t1 <+> "~" <+> pretty t2

data Coercion
  = AxiomCoercion AxiomName (Vector Type)
  | VarCoercion CoercionVar
  | TypeCtorCoercion TypeCtor (Vector Coercion)
  | FamilyCoercion Family (Vector Coercion)
  | ReflCoercion Type
  | TransCoercion Coercion Coercion
  | SymmCoercion Coercion
  | EquivalentCoercion Coercion Coercion
  deriving (Generic, Show, Eq)

instance Pretty Coercion where
  pretty (AxiomCoercion n tys) = hsep (pretty n : map (("@" <>) . prettyAtomType) (Vector.toList tys))
  pretty (VarCoercion v) = pretty v
  pretty (TypeCtorCoercion k cs) = hsep (pretty k : map prettyAtomCoercion (Vector.toList cs))
  pretty (FamilyCoercion k cs) = "<" <> hsep (pretty k : map prettyAtomCoercion (Vector.toList cs)) <> ">"
  pretty (ReflCoercion t) = "<" <> pretty t <> ">"
  pretty (TransCoercion c1 c2) = prettyAtomCoercion c1 <+> "∘" <+> prettyAtomCoercion c2
  pretty (SymmCoercion c) = "sym" <+> prettyAtomCoercion c
  pretty (EquivalentCoercion c1 c2) = prettyAtomCoercion c1 <+> ", " <+> prettyAtomCoercion c2

prettyAtomCoercion :: Coercion -> Doc ann
prettyAtomCoercion c@VarCoercion {} = pretty c
prettyAtomCoercion c@FamilyCoercion {} = pretty c
prettyAtomCoercion c@ReflCoercion {} = pretty c
prettyAtomCoercion c = parens (pretty c)
