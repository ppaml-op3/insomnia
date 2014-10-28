{-# LANGUAGE ViewPatterns #-}
module Insomnia.Typecheck.Selfify
       (selfifyModelType
       , selfifyTypeDefn
       ) where

import Data.Maybe (mapMaybe)
import Data.Monoid (Monoid(..))

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier (Path(..), Identifier)
import Insomnia.Types (Con(..))
import Insomnia.Expr (QVar(..))
import Insomnia.TypeDefn (TypeDefn(..), ConstructorDef(..))
import Insomnia.ModelType (Signature(..), TypeSigDecl(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig (SelfSig(..))

-- | "Selfification" (c.f. TILT) is the process of adding to the current scope
-- a type variable of singleton kind (ie, a module variable standing
-- for a module expression) such that the module variable is given its principal
-- kind (exposes maximal sharing).
selfifyModelType :: Path -> Signature -> TC SelfSig
selfifyModelType pmod msig_ =
  case msig_ of
    UnitSig -> return UnitSelfSig
    ValueSig fld ty msig -> do
      let qvar = QVar (ProjP pmod fld)
      selfSig <- selfifyModelType pmod msig
      return $ ValueSelfSig qvar ty selfSig
    TypeSig fld bnd ->
      U.lunbind bnd $ \((tyId, U.unembed -> tsd), msig) -> do
      let p = ProjP pmod fld
          -- replace the local Con (IdP tyId) way of refering to
          -- this definition in the rest of the signature by
          -- the full projection from the model path.  Also replace the
          -- type constructors
          substitution_ = selfifyTypeSigDecl pmod tsd
          substitution = (tyId, p) : substitution_
          tsd' = U.substs substitution tsd
          msig' = U.substs substitution msig
      selfSig <- selfifyModelType pmod msig'
      return $ TypeSelfSig (Con p) tsd' selfSig
  

selfifyTypeSigDecl :: Path -> TypeSigDecl -> [(Identifier, Path)]
selfifyTypeSigDecl pmod tsd =
  case tsd of
    AbstractTypeSigDecl _k -> mempty
    ManifestTypeSigDecl defn -> selfifyTypeDefn pmod defn

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

