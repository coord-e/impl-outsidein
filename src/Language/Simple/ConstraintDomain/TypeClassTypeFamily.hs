-- Implementation of X for type classes and type families, as described in §7.
module Language.Simple.ConstraintDomain.TypeClassTypeFamily
  ( TypeClassTypeFamily,
    ExtensionMonotype (..),
    ExtensionConstraint (..),
    ExtensionTypeError (..),
    Class (..),
    Family (..),
  )
where

import Language.Simple.ConstraintDomain.TypeClassTypeFamily.Extension
  ( Class (..),
    ExtensionConstraint (..),
    ExtensionMonotype (..),
    ExtensionTypeError (..),
    Family (..),
    TypeClassTypeFamily,
  )
import Language.Simple.ConstraintDomain.TypeClassTypeFamily.Solver ()
