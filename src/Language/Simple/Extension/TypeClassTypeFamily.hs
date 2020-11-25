-- Implementation of X for type classes and type families, as described in §7.
module Language.Simple.Extension.TypeClassTypeFamily
  ( TypeClassTypeFamily,
    ExtensionMonotype (..),
    ExtensionConstraint (..),
    ExtensionTypeError (..),
    Class (..),
    Family (..),
  )
where

import Language.Simple.Extension.TypeClassTypeFamily.Extension
  ( Class (..),
    ExtensionConstraint (..),
    ExtensionMonotype (..),
    ExtensionTypeError (..),
    Family (..),
    TypeClassTypeFamily,
  )
import Language.Simple.Extension.TypeClassTypeFamily.Solver ()
