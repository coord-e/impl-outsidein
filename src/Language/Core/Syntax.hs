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
    printProgram,
    simpleDataCtorType,
    CompleteTermVarBinder,
    CompleteExpr,
    takePropositionLhs,
    takePropositionRhs,
    CompleteProposition,
    CompleteCaseArm,
    CompleteCoercion,
    prettyAtomExpr,
    prettyAtomType,
    prettyAtomCoercion,
    CompleteCoercionVarBinder,
    AxiomName (..),
    AxiomScheme (..),
    DataCtorType (..),
    Expr (..),
    TermVarBinder (..),
    CoercionVarBinder (..),
    ImplicationId (..),
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
import qualified Data.HashMap.Strict as HashMap (toList)
import Data.Hashable (Hashable)
import Data.Text (Text, pack)
import qualified Data.Text as Text (unlines, unwords)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (empty, fromList, null, toList)
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Simple.Fresh (GenFresh (..))
import Language.Simple.Syntax
  ( Class (..),
    DataCtor (..),
    Family (..),
    TermVar (..),
    TypeVar (..),
  )
import Numeric.Natural (Natural)
import Prettyprinter
  ( Doc,
    Pretty (..),
    align,
    defaultLayoutOptions,
    hsep,
    layoutPretty,
    line,
    nest,
    parens,
    punctuate,
    sep,
    space,
    unsafeViaShow,
    vsep,
    (<+>),
  )
import Prettyprinter.Internal (unsafeTextWithoutNewlines)
import Prettyprinter.Render.Text (renderStrict)

data Program = Program
  { bindings :: Vector Binding,
    axioms :: HashMap AxiomName AxiomScheme,
    vars :: HashMap TermVar CompleteType,
    dataCtors :: HashMap DataCtor DataCtorType
  }
  deriving (Generic, Show, Eq)

printProgram :: Program -> Text
printProgram Program {bindings, axioms, vars, dataCtors} =
  Text.unlines
    ( axiomTexts <> varTexts <> dataCtorTexts <> bindingTexts
    )
  where
    bindingTexts = map printBinding (Vector.toList bindings)
    axiomTexts = map printAxiom (HashMap.toList axioms)
    varTexts = map printVar (HashMap.toList vars)
    dataCtorTexts = map printDataCtor (HashMap.toList dataCtors)
    printBinding b = "let " <> printPretty b
    printAxiom (n, s) = Text.unwords ["axiom", printPretty n, "=", printPretty s]
    printVar (x, t) = Text.unwords ["type", printPretty x, "::", printPretty t]
    printDataCtor (k, d) = Text.unwords ["data", printPretty k, "::", printPretty d]
    printPretty :: Pretty a => a -> Text
    printPretty = renderStrict . layoutPretty defaultLayoutOptions . pretty

data Binding = Binding CompleteTermVarBinder CompleteExpr
  deriving (Generic, Show, Eq)

instance Pretty Binding where
  pretty (Binding b e) = pretty b <+> "=" <> nest 2 (line <> pretty e)

data AxiomScheme = ForallAxiomScheme
  { vars :: Vector TypeVar,
    lhs :: CompleteType,
    rhs :: CompleteType
  }
  deriving (Generic, Show, Eq)

instance Pretty AxiomScheme where
  pretty ForallAxiomScheme {vars, lhs, rhs} =
    align $
      sep
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
    align (sep [forall_, exists, coerExists, ty])
    where
      forall_ = "∀" <> hsep (map pretty $ Vector.toList universalVars) <> "."
      exists = "∃" <> hsep (map pretty $ Vector.toList existentialVars) <> "."
      coerExists = "∃" <> hsep (map (parens . pretty) $ Vector.toList coercionVars) <> "."
      fs = map pretty (Vector.toList fields)
      ret = pretty (ApplyType ctor (fmap VarType ctorArgs) :: CompleteType)
      ty = align (sep (punctuate " →" (fs <> [ret])))

simpleDataCtorType :: Text -> DataCtorType
simpleDataCtorType x = DataCtorType Vector.empty Vector.empty Vector.empty Vector.empty (NamedTypeCtor x) Vector.empty

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
  | LetExpr (Maybe ImplicationId) (TermVarBinder a) (Expr a c d) (Expr a c d)
  | CastExpr (Expr a c d) (Coercion a c)
  deriving (Generic, Show, Eq)

type CompleteExpr = Expr Void Void Void

instance (Pretty a, Pretty c, Pretty d) => Pretty (Expr a c d) where
  pretty (UnsolvedClassDictionaryExpr d) = pretty d
  pretty (CtorExpr k) = pretty k
  pretty (VarExpr x) = pretty x
  pretty (LambdaExpr b e) = "λ" <> parens (pretty b) <> "." <> lambdaBody e
  pretty (TypeLambdaExpr v e) = "Λ" <> pretty v <> "." <> lambdaBody e
  pretty (CoercionLambdaExpr b e) = "Λ" <> parens (pretty b) <> "." <> lambdaBody e
  pretty (ApplyExpr e1 e2) = nested e1 <+> prettyAtomExpr e2
    where
      nested e@ApplyExpr {} = pretty e
      nested e@TypeApplyExpr {} = pretty e
      nested e@CoercionApplyExpr {} = pretty e
      nested e@CtorExpr {} = pretty e
      nested e@VarExpr {} = pretty e
      nested e@UnsolvedClassDictionaryExpr {} = pretty e
      nested e = parens (pretty e)
  pretty (TypeApplyExpr e t) = pretty e <+> "@" <> prettyAtomType t
  pretty (CoercionApplyExpr e c) = pretty e <+> "@" <> prettyAtomCoercion c
  pretty (CaseExpr e t arms) =
    "case" <+> pretty e <+> "→"
      <+> pretty t
      <+> "{" <> nest 2 (line <> vsep (punctuate ", " (map pretty $ Vector.toList arms))) <> line <> "}"
  pretty (LetExpr Nothing b e1 e2) = "let" <+> pretty b <+> "=" <+> pretty e1 <+> "in" <+> pretty e2
  pretty (LetExpr (Just id) b e1 e2) = "let" <+> parens (pretty id) <+> pretty b <+> "=" <+> pretty e1 <+> "in" <+> pretty e2
  pretty (CastExpr e c) = pretty e <+> "▹" <+> pretty c

lambdaBody :: (Pretty a, Pretty c, Pretty d) => Expr a c d -> Doc ann
lambdaBody e
  | isLambdaExpr e = space <> pretty e
  | otherwise = nest 2 (line <> pretty e)
  where
    isLambdaExpr LambdaExpr {} = True
    isLambdaExpr TypeLambdaExpr {} = True
    isLambdaExpr CoercionLambdaExpr {} = True
    isLambdaExpr _ = False

prettyAtomExpr :: (Pretty a, Pretty c, Pretty d) => Expr a c d -> Doc ann
prettyAtomExpr e@ApplyExpr {} = parens (pretty e)
prettyAtomExpr e@TypeApplyExpr {} = parens (pretty e)
prettyAtomExpr e@CoercionApplyExpr {} = parens (pretty e)
prettyAtomExpr e@CastExpr {} = parens (pretty e)
prettyAtomExpr e = pretty e

newtype ImplicationId = ImplicationId Natural
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance GenFresh ImplicationId where
  fromFreshNatural = ImplicationId

instance Pretty ImplicationId where
  pretty (ImplicationId n) = "%b" <> unsafeViaShow n

data CaseArm a c d = CaseArm
  { implicationId :: Maybe ImplicationId,
    ctor :: DataCtor,
    typeArgs :: Vector (Type a),
    existentialVars :: Vector TypeVar,
    coercionVars :: Vector (CoercionVarBinder a),
    termVars :: Vector (TermVarBinder a),
    body :: Expr a c d
  }
  deriving (Generic, Show, Eq)

type CompleteCaseArm = CaseArm Void Void Void

instance (Pretty a, Pretty c, Pretty d) => Pretty (CaseArm a c d) where
  pretty CaseArm {implicationId, ctor, typeArgs, existentialVars, coercionVars, termVars, body} =
    lhs <+> "=>" <> nest 2 (line <> pretty body)
    where
      lhs =
        hsep
          ( implicId :
            pretty ctor :
            map (("@" <>) . prettyAtomType) (Vector.toList typeArgs)
              <> map ((">" <>) . pretty) (Vector.toList existentialVars)
              <> map ((">" <>) . parens . pretty) (Vector.toList coercionVars)
              <> map (parens . pretty) (Vector.toList termVars)
          )
      implicId =
        case implicationId of
          Just id -> parens (pretty id)
          Nothing -> mempty

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
  pretty FunctionTypeCtor = "(→)"

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
    | isNested t1 = parens (pretty t1) <+> "→" <+> pretty t2
    | otherwise = pretty t1 <+> "→" <+> pretty t2
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

instance GenFresh CoercionVar where
  fromFreshNatural = CoercionVar . pack . ("'c" ++) . show

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
  | RightCoercion Int (Coercion a c)
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
  pretty (RightCoercion n c) = prettyAtomCoercion c <> "[" <> pretty n <> "]"
  pretty (ReflCoercion t) = "<" <> pretty t <> ">"
  pretty (TransCoercion c1 c2) = pretty c1 <+> "∘" <+> nested c2
    where
      nested c@TransCoercion {} = parens (pretty c)
      nested c = pretty c
  pretty (SymmCoercion c) = "sym" <+> prettyAtomCoercion c
  pretty (EquivalentCoercion c1 c2) = prettyAtomCoercion c1 <> "," <+> prettyAtomCoercion c2

prettyAtomCoercion :: (Pretty a, Pretty c) => Coercion a c -> Doc ann
prettyAtomCoercion c@UnsolvedCoercion {} = pretty c
prettyAtomCoercion c@VarCoercion {} = pretty c
prettyAtomCoercion c@FamilyCoercion {} = pretty c
prettyAtomCoercion c@ReflCoercion {} = pretty c
prettyAtomCoercion c@RightCoercion {} = pretty c
prettyAtomCoercion c = parens (pretty c)
