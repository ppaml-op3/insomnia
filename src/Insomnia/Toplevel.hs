-- | "Toplevel" definitions.
--
module Insomnia.Toplevel where

import Insomnia.Identifier
import Insomnia.ModuleType
import Insomnia.Module
import Insomnia.Query

-- | A toplevel contains a list of toplevel items.
--
-- TODO: worth representing this stuff using Unbound binders?
newtype Toplevel = Toplevel [ToplevelItem]
                   deriving Show

-- | Each toplevel item is either the binding of
-- a module name to a module expression, or the binding of a module
-- type name to a module type expression, or an import from a
-- subordinate toplevel (separate file).
data ToplevelItem =
  ToplevelModule Identifier ModuleExpr
  | ToplevelModuleType SigIdentifier ModuleType
    -- | The idea is that a surface language toplevel declaration
    --   import "foo.ism" (module type T module M using N)
    -- is translated into:
    --   toplevel ^foo "foo.ism"
    --   module type T = ^foo:T
    --   module M = ^foo:N
    --   
    -- So a Toplevel is really like a transparent module definition
    -- except unlike surface language modules, toplevels are allowed
    -- to contain module types (and not allowed to contain type or
    -- value bindings).  In FΩ of course these distinctions disappear.
  | ToplevelImported FilePath TopRef Toplevel
  | ToplevelQuery QueryExpr
    deriving Show
