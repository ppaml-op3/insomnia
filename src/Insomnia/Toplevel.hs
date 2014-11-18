-- | "Toplevel" definitions.
--
module Insomnia.Toplevel where

import Insomnia.Identifier
import Insomnia.ModelType
import Insomnia.Model

-- | A toplevel contains a list of toplevel items.
--
-- TODO: worth representing this stuff using Unbound binders?
newtype Toplevel = Toplevel [ToplevelItem]
                   deriving Show

-- | Each toplevel item is either the binding of
-- a model name to a model expression, or
-- the binding of a model type name to a model type expression.
data ToplevelItem =
  ToplevelModel Identifier ModelExpr
  | ToplevelModelType SigIdentifier ModelType
    deriving Show
