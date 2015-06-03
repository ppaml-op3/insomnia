{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Typecheck.Equiv.TypeAlias (equivTypeAlias) where

import Control.Monad (unless)
import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier (Field)
import Insomnia.TypeDefn (TypeAlias(..), PrettyField(..))
import Insomnia.Types

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.TypeDefn (checkTypeAlias)

-- | Check that two given type aliases are equivalent.
equivTypeAlias :: Field -> TypeAlias -> TypeAlias -> TC ()
equivTypeAlias fld alias1_ alias2_ = do
  (alias1, info1) <- checkTypeAlias alias1_
  (alias2, info2) <- checkTypeAlias alias2_
  let k1 = typeAliasInfoKind info1
      k2 = typeAliasInfoKind info2
  unless (k1 `U.aeq` k2) $
    typeError ("Type alias " <> formatErr (PrettyField fld alias1_)
               <> " has kind " <> formatErr k1
               <> " which conflicts with kind " <> formatErr k2
               <> " of the alias " <> formatErr (PrettyField fld alias2_))
  generalizeK k1 $ \tvks -> do
    let tyargs = map (\(tv, _k) -> TV tv) tvks
    t1 <- expandAndApply alias1 tyargs
    t2 <- expandAndApply alias2 tyargs
    unless (t1 `U.aeq` t2) $
      typeError ("Type aliases " <> formatErr (PrettyField fld alias1_)
                 <> " and "
                 <> formatErr (PrettyField fld alias2_)
                 <> " expand to different types. ("
                 <> formatErr t1
                 <> " and "
                 <> formatErr t2
                 <> ", respectively.)")
    

-- | @generalizeK (k1 `KArr` k2 `KArr` ... kN `KArr` KType) cont@ calls
-- @cont [(a1, k1), ... (aN, kN)]@ where the @a@'s are fresh.
generalizeK :: Kind -> ([(TyVar, Kind)] -> TC a) -> TC a
generalizeK k kont =
  case k of
    KType -> kont []
    KArr k1 ks -> do
      a1 <- U.lfresh (U.s2n "a")
      extendTyVarCtx a1 k1
        $ generalizeK ks
        $ \tvks -> kont $ (a1, k1):tvks
        
      
-- | Given a type alias @type t a1 .... aN = tRHS@ and a list of types
-- @[t1, ...., tN, s1, .... sM]@ returns
-- @tRHS[t1/a1, ... tN/aN] `TApp` s1 `TApp` ... `TApp` sM@
expandAndApply :: TypeAlias -> [Type] -> TC Type
expandAndApply (ManifestTypeAlias bnd) tAllArgs =
  U.lunbind bnd $ \(tparamks, ty) ->
  return $ let tparams = map fst tparamks
               n = length tparamks
               (tsubArgs, tappArgs) = splitAt n tAllArgs
               substitution = zip tparams tsubArgs
               tRHS = U.substs substitution ty
           in tRHS `tApps ` tappArgs
expandAndApply (DataCopyTypeAlias tp _defn) tAllArgs =
  return $ (TC $ TCGlobal tp) `tApps` tAllArgs
