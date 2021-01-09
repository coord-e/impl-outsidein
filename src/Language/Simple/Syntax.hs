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
    Family (..),
    Class (..),
    SimpleMonotype,
    functionType,
    prettyAtomMonotype,
    TypeVar (..),
    TypeCtor (..),
    Constraint (..),
    SimpleConstraint,
  )
where

import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Text (Text, pack)
import Data.Vector (Vector)
import qualified Data.Vector as Vector (fromList, toList)
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Simple.Fresh (GenFresh (..))
import Prettyprinter (Doc, Pretty (..), hsep, parens, space, (<+>))
import Prettyprinter.Internal (unsafeTextWithoutNewlines)

-- | Program to be typed.
-- We include top-level axiom schemes and types of data constructors here for brevity.
data Program = Program
  { -- | Sequence of top-level bindings
    bindings :: Vector Binding,
    -- | Sequence of top-level axiom schemes.
    -- We represent a set of schemes using sequence instead of product for brevity.
    axioms :: Vector AxiomScheme,
    -- | Types of variables used to build initial type environment.
    vars :: HashMap TermVar TypeScheme,
    -- | Types of data constructors.
    dataCtors :: HashMap DataCtor DataCtorType
  }
  deriving (Generic)

-- | Top-level binding in the program.
data Binding
  = -- | Unannotated binding. \( f = e \)
    UnannotatedBinding TermVar Expr
  | -- | Annotated binding. \( f :: \sigma = e \)
    AnnotatedBinding TermVar TypeScheme Expr
  deriving (Generic)

-- | Top-level axiom scheme. \( \forall \bar{a} . Q_1 \Rightarrow Q_2 \)
data AxiomScheme = ForallAxiomScheme
  { -- | Type variables to be quantified.
    vars :: Vector TypeVar,
    -- | Constraint for the quantified variables.
    constraint :: SimpleConstraint,
    -- | The axiom.
    head :: SimpleConstraint
  }
  deriving (Generic)

-- | Type of data constructor. \( \forall \bar{a} \bar{b}. Q \Rightarrow \bar{v} \rightarrow T \bar{a} \)
data DataCtorType = DataCtorType
  { -- | Universally quantified variables.
    universalVars :: Vector TypeVar,
    -- | Existentially quantified variables.
    existentialVars :: Vector TypeVar,
    -- | Constraint for the quantified variables.
    constraint :: SimpleConstraint,
    -- | Field types of the data constructor.
    fields :: Vector SimpleMonotype,
    -- | Type-level constructor that corresponds to the data constructor.
    ctor :: TypeCtor,
    -- | Type-level arguments to the type constructor.
    ctorArgs :: Vector TypeVar
  }
  deriving (Generic)

-- | Expression.
data Expr
  = -- | Data constructor. \( K \)
    CtorExpr DataCtor
  | -- | Term variable. \( x \)
    VarExpr TermVar
  | -- | Function abstraction. \( \lambda x . e \)
    LambdaExpr TermVar Expr
  | -- | Function application. \( e_1 e_2 \)
    ApplyExpr Expr Expr
  | -- | Pattern matching. \( \texttt{case} e \texttt{of} \{ \bar{ K \bar{x} \rightarrow e } \} \)
    CaseExpr Expr (Vector CaseArm)
  | -- | Unannotated let binding. \( \texttt{let} x = e_1 \texttt{in} e_2 \)
    UnannotatedLetExpr TermVar Expr Expr
  | -- | Annotated let binding. \( \texttt{let} x \texttt{::} \sigma = e_1 \texttt{in} e_2 \)
    AnnotatedLetExpr TermVar TypeScheme Expr Expr
  deriving (Generic)

-- | Arm in @case@ expression. \( \bar{ K \bar{x} \rightarrow e } \)
data CaseArm = CaseArm
  { -- | The data constructor to be matched.
    ctor :: DataCtor,
    -- | Variable bindings in the pattern.
    vars :: Vector TermVar,
    -- | The right-hand side of the arm.
    body :: Expr
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
data DataCtor
  = NamedDataCtor Text
  | IntegerDataCtor Integer
  deriving stock (Show, Ord, Eq, Generic)
  deriving anyclass (Hashable)

instance Pretty DataCtor where
  pretty (NamedDataCtor k) = unsafeTextWithoutNewlines k
  pretty (IntegerDataCtor i) = pretty i

-- | Type scheme.
data TypeScheme = ForallTypeScheme
  { -- | Type variables to be quantified.
    vars :: Vector TypeVar,
    -- | Constraint for the quantified variables.
    constraint :: SimpleConstraint,
    -- | The type.
    monotype :: SimpleMonotype
  }
  deriving (Generic)

instance Pretty TypeScheme where
  pretty ForallTypeScheme {vars, constraint, monotype} = quant <> qual constraint <> pretty monotype
    where
      quant
        | null vars = mempty
        | otherwise = "forall" <+> hsep (map pretty (Vector.toList vars)) <> "." <> space
      qual EmptyConstraint = mempty
      qual q = pretty q <+> "=>" <> space

-- | Type family.
newtype Family = Family Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty Family where
  pretty (Family x) = unsafeTextWithoutNewlines x

-- | Monotype that contains unification variable as @a@.
data Monotype a
  = -- | Rigid type variable. \( a \)
    VarType TypeVar
  | -- | Type constructor application. \( T \bar{\tau} \)
    ApplyType TypeCtor (Vector (Monotype a))
  | -- | Unification type variable. \( \alpha \)
    UniType a
  | -- | Type family application. \( F \bar{\tau} \)
    FamilyApplyType Family (Vector (Monotype a))
  deriving (Generic)

instance Functor Monotype where
  fmap _ (VarType v) = VarType v
  fmap f (ApplyType k ts) = ApplyType k $ fmap (fmap f) ts
  fmap f (UniType a) = UniType $ f a
  fmap f (FamilyApplyType k ts) = FamilyApplyType k $ fmap (fmap f) ts

type SimpleMonotype = Monotype Void

functionType :: Monotype a -> Monotype a -> Monotype a
functionType a b = ApplyType FunctionTypeCtor $ Vector.fromList [a, b]

instance Pretty a => Pretty (Monotype a) where
  pretty (VarType v) = pretty v
  pretty (UniType a) = pretty a
  pretty (ApplyType FunctionTypeCtor (Vector.toList -> [a, b]))
    | isNested a = parens (pretty a) <+> "->" <+> pretty b
    | otherwise = pretty a <+> "->" <+> pretty b
    where
      isNested (ApplyType FunctionTypeCtor _) = True
      isNested _ = False
  pretty (ApplyType k ts) = hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))
  pretty (FamilyApplyType k ts) = "<" <> hsep (pretty k : map prettyAtomMonotype (Vector.toList ts)) <> ">"

prettyAtomMonotype :: Pretty a => Monotype a -> Doc ann
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

-- | Type class.
newtype Class = Class Text
  deriving stock (Ord, Eq, Generic)
  deriving newtype (Show)
  deriving anyclass (Hashable)

instance Pretty Class where
  pretty (Class x) = unsafeTextWithoutNewlines x

-- | Constraint that contains unification variable as @a@.
data Constraint a
  = -- | \( \epsilon \)
    EmptyConstraint
  | -- | Product of two constraints. \( Q_1 \land Q_2 \)
    ProductConstraint (Constraint a) (Constraint a)
  | -- | Equality constraint of two types. \( \tau_1 \sim \tau_2 \)
    EqualityConstraint (Monotype a) (Monotype a)
  | -- | Type class constraint. \( C \bar{\tau} \).
    TypeClassConstraint Class (Vector (Monotype a))
  deriving (Generic)

instance Functor Constraint where
  fmap _ EmptyConstraint = EmptyConstraint
  fmap f (ProductConstraint q1 q2) = ProductConstraint (fmap f q1) (fmap f q2)
  fmap f (EqualityConstraint t1 t2) = EqualityConstraint (fmap f t1) (fmap f t2)
  fmap f (TypeClassConstraint k ts) = TypeClassConstraint k $ fmap (fmap f) ts

type SimpleConstraint = Constraint Void

instance Semigroup (Constraint a) where
  (<>) = ProductConstraint

instance Monoid (Constraint a) where
  mempty = EmptyConstraint

instance Pretty a => Pretty (Constraint a) where
  pretty EmptyConstraint = "ε"
  pretty (ProductConstraint q1 q2) = pretty q1 <+> "∧" <+> pretty q2
  pretty (EqualityConstraint t1 t2) = prettyAtomMonotype t1 <+> "~" <+> prettyAtomMonotype t2
  pretty (TypeClassConstraint k ts) = hsep (pretty k : map prettyAtomMonotype (Vector.toList ts))
