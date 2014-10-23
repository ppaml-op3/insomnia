module Insomnia.Typecheck.Selfify where

import Data.Maybe (mapMaybe)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier (Path(..), Identifier)
import Insomnia.Types (Con(..))
import Insomnia.TypeDefn (TypeDefn(..), ConstructorDef(..))

-- | Given the path to a type defintion and the type definition, construct
-- a substitution that replaces unqualified references to the components of
-- the definition (for example the value constructors of an algebraic datatype)
-- by their qualified names with respect to the given path.
selfifyTypeDefn :: Path -> TypeDefn -> [(Identifier, Path)]
selfifyTypeDefn _pmod (EnumDefn _) = []
selfifyTypeDefn pmod (DataDefn bnd) = let
  (_, constrDefs) = UU.unsafeUnbind bnd
  cs = map (\(ConstructorDef c _) -> c) constrDefs
  in mapMaybe (mkSubst pmod) cs
  where
    mkSubst :: Path -> Con -> Maybe (Identifier, Path)
    mkSubst p (Con (IdP short)) = let fld = U.name2String short
                                      long = ProjP p fld
                                  in Just (short, long)
    mkSubst _ _                 = Nothing
