{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Simple.Syntax
  ( -- * Programs
    Program (..),
    Binding (..),
    AxiomScheme (..),
    DataCtorType (..),

    -- * Expressions
    Expr (..),
    CaseArm (..),
    TermVar (..),
    DataCtor (..),

    -- * Types
    TypeScheme (..),
    Monotype (..),
    SimpleMonotype,
    ExtensionMonotype,
    functionType,
    prettyAtomMonotype,
    TypeVar (..),
    TypeCtor (..),
    Constraint (..),
    SimpleConstraint,
    ExtensionConstraint,
  )
where

import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Kind (Type)
import Data.Text (Text, pack)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, toList)
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Simple.Fresh (GenFresh (..))
import Prettyprinter (Doc, Pretty (..), hsep, parens, space, (<+>))
import Prettyprinter.Internal (unsafeTextWithoutNewlines)

data family ExtensionMonotype x :: Type -> Type

data family ExtensionConstraint x :: Type -> Type

-- | Program to be typed.
-- We include top-level axiom schemes and types of data constructors here for brevity.
data Program x = Program
  { -- | Sequence of top-level bindings
    bindings :: Vector (Binding x),
    -- | Sequence of top-level axiom schemes.
    -- We represent a set of schemes using sequence instead of product for brevity.
    axioms :: Vector (AxiomScheme x),
    -- | Types of variables used to build initial type environment.
    vars :: HashMap TermVar (TypeScheme x),
    -- | Types of data constructors.
    dataCtors :: HashMap DataCtor (DataCtorType x)
  }
  deriving (Generic)

-- | Top-level binding in the program.
data Binding x
  = -- | Unannotated binding. \( f = e \)
    UnannotatedBinding TermVar (Expr x)
  | -- | Annotated binding. \( f :: \sigma = e \)
    AnnotatedBinding TermVar (TypeScheme x) (Expr x)
  deriving (Generic)

-- | Top-level axiom scheme. \( \forall \bar{a} . Q_1 \Rightarrow Q_2 \)
data AxiomScheme x = ForallAxiomScheme
  { -- | Type variables to be quantified.
    vars :: Vector TypeVar,
    -- | Constraint for the quantified variables.
    constraint :: SimpleConstraint x,
    -- | The axiom.
    head :: SimpleConstraint x
  }
  deriving (Generic)

-- | Type of data constructor. \( \forall \bar{a} \bar{b}. Q \Rightarrow \bar{v} \rightarrow T \bar{a} \)
data DataCtorType x = DataCtorType
  { -- | Universally quantified variables.
    universalVars :: Vector TypeVar,
    -- | Existentially quantified variables.
    existentialVars :: Vector TypeVar,
    -- | Constraint for the quantified variables.
    constraint :: SimpleConstraint x,
    -- | Field types of the data constructor.
    fields :: Vector (SimpleMonotype x),
    -- | Type-level constructor that corresponds to the data constructor.
    ctor :: TypeCtor,
    -- | Type-level arguments to the type constructor.
    ctorArgs :: Vector TypeVar
  }
  deriving (Generic)

-- | Expression.
data Expr x
  = -- | Data constructor. \( K \)
    CtorExpr DataCtor
  | -- | Term variable. \( x \)
    VarExpr TermVar
  | -- | Function abstraction. \( \lambda x . e \)
    LambdaExpr TermVar (Expr x)
  | -- | Function application. \( e_1 e_2 \)
    ApplyExpr (Expr x) (Expr x)
  | -- | Pattern matching. \( \texttt{case} e \texttt{of} \{ \bar{ K \bar{x} \rightarrow e } \} \)
    CaseExpr (Expr x) (Vector (CaseArm x))
  | -- | Unannotated let binding. \( \texttt{let} x = e_1 \texttt{in} e_2 \)
    UnannotatedLetExpr TermVar (Expr x) (Expr x)
  | -- | Annotated let binding. \( \texttt{let} x \texttt{::} \sigma = e_1 \texttt{in} e_2 \)
    AnnotatedLetExpr TermVar (TypeScheme x) (Expr x) (Expr x)
  deriving (Generic)

-- | Arm in @case@ expression. \( \bar{ K \bar{x} \rightarrow e } \)
data CaseArm x = CaseArm
  { -- | The data constructor to be matched.
    ctor :: DataCtor,
    -- | Variable bindings in the pattern.
    vars :: Vector TermVar,
    -- | The right-hand side of the arm.
    body :: Expr x
  }
  deriving (Generic)

-- | Term-level variable.
newtype TermVar = TermVar Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty TermVar where
  pretty (TermVar x) = unsafeTextWithoutNewlines x

-- | Data constructor.
newtype DataCtor = DataCtor Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty DataCtor where
  pretty (DataCtor k) = unsafeTextWithoutNewlines k

-- | Type scheme.
data TypeScheme x = ForallTypeScheme
  { -- | Type variables to be quantified.
    vars :: Vector TypeVar,
    -- | Constraint for the quantified variables.
    constraint :: SimpleConstraint x,
    -- | The type.
    monotype :: SimpleMonotype x
  }
  deriving (Generic)

instance (Pretty (ExtensionMonotype x Void), Pretty (ExtensionConstraint x Void)) => Pretty (TypeScheme x) where
  pretty ForallTypeScheme {vars, constraint, monotype} = quant <> qual constraint <> pretty monotype
    where
      quant
        | null vars = mempty
        | otherwise = "forall" <+> hsep (map pretty (Vector.toList vars)) <> "." <> space
      qual EmptyConstraint = mempty
      qual q = pretty q <+> "=>" <> space

-- | Monotype that contains unification variable as @a@.
data Monotype x a
  = -- | Rigid type variable. \( a \)
    VarType TypeVar
  | -- | Type constructor application. \( T \bar{\tau} \)
    ApplyType TypeCtor (Vector (Monotype x a))
  | -- | Unification type variable. \( \alpha \)
    UniType a
  | -- | Type from extension @x@.
    ExtensionType (ExtensionMonotype x a)
  deriving (Generic)

instance Functor (ExtensionMonotype x) => Functor (Monotype x) where
  fmap _ (VarType v) = VarType v
  fmap f (ApplyType k ts) = ApplyType k $ fmap (fmap f) ts
  fmap f (UniType a) = UniType $ f a
  fmap f (ExtensionType x) = ExtensionType $ fmap f x

type SimpleMonotype x = Monotype x Void

functionType :: Monotype x a -> Monotype x a -> Monotype x a
functionType a b = ApplyType FunctionTypeCtor $ Vector.fromList [a, b]

instance (Pretty (ExtensionMonotype x a), Pretty a) => Pretty (Monotype x a) where
  pretty (VarType v) = pretty v
  pretty (UniType a) = pretty a
  pretty (ApplyType FunctionTypeCtor (Vector.toList -> [a, b]))
    | isNested a = parens (pretty a) <+> "->" <+> pretty b
    | otherwise = pretty a <+> "->" <+> pretty b
    where
      isNested (ApplyType FunctionTypeCtor _) = True
      isNested _ = False
  pretty (ApplyType k ts) = hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))
  pretty (ExtensionType x) = pretty x

prettyAtomMonotype :: (Pretty (ExtensionMonotype x a), Pretty a) => Monotype x a -> Doc ann
prettyAtomMonotype t@(ApplyType _ ts') | not (null ts') = parens (pretty t)
prettyAtomMonotype t = pretty t

-- | Type constructor.
data TypeCtor
  = NamedTypeCtor Text
  | FunctionTypeCtor
  deriving stock (Show, Ord, Eq, Generic)
  deriving anyclass (Hashable)

instance Pretty TypeCtor where
  pretty (NamedTypeCtor k) = unsafeTextWithoutNewlines k
  pretty FunctionTypeCtor = "(->)"

-- | Type-level variable.
newtype TypeVar = TypeVar Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty TypeVar where
  pretty (TypeVar v) = unsafeTextWithoutNewlines v

instance GenFresh TypeVar where
  fromFreshNatural = TypeVar . pack . ("a" ++) . show

-- | Constraint that contains unification variable as @a@.
data Constraint x a
  = -- | \( \epsilon \)
    EmptyConstraint
  | -- | Product of two constraints. \( Q_1 \land Q_2 \)
    ProductConstraint (Constraint x a) (Constraint x a)
  | -- | Equality constraint of two types. \( \tau_1 \sim \tau_2 \)
    EqualityConstraint (Monotype x a) (Monotype x a)
  | -- | Constraint from extension @x@.
    ExtensionConstraint (ExtensionConstraint x a)
  deriving (Generic)

instance
  ( Functor (ExtensionConstraint x),
    Functor (ExtensionMonotype x)
  ) =>
  Functor (Constraint x)
  where
  fmap _ EmptyConstraint = EmptyConstraint
  fmap f (ProductConstraint q1 q2) = ProductConstraint (fmap f q1) (fmap f q2)
  fmap f (EqualityConstraint t1 t2) = EqualityConstraint (fmap f t1) (fmap f t2)
  fmap f (ExtensionConstraint x) = ExtensionConstraint $ fmap f x

type SimpleConstraint x = Constraint x Void

instance Semigroup (Constraint x a) where
  (<>) = ProductConstraint

instance Monoid (Constraint x a) where
  mempty = EmptyConstraint

instance
  ( Pretty (ExtensionMonotype x a),
    Pretty (ExtensionConstraint x a),
    Pretty a
  ) =>
  Pretty (Constraint x a)
  where
  pretty EmptyConstraint = "ε"
  pretty (ProductConstraint q1 q2) = pretty q1 <+> "∧" <+> pretty q2
  pretty (EqualityConstraint t1 t2) = prettyAtomMonotype t1 <+> "~" <+> prettyAtomMonotype t2
  pretty (ExtensionConstraint x) = pretty x
