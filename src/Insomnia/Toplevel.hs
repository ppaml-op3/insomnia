-- | "Toplevel" definitions.
--
module Insomnia.Toplevel where

import Insomnia.Identifier
import Insomnia.ModuleType
import Insomnia.Module

-- | A toplevel contains a list of toplevel items.
--
-- TODO: worth representing this stuff using Unbound binders?
newtype Toplevel = Toplevel [ToplevelItem]
                   deriving Show

-- | Each toplevel item is either the binding of
-- a module name to a module expression, or
-- the binding of a module type name to a module type expression.
data ToplevelItem =
  ToplevelModule Identifier ModuleExpr
  | ToplevelModuleType SigIdentifier ModuleType
    deriving Show
