{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Typecheck.Equiv.TypeDefn (equivTypeDefn) where

import Control.Monad (zipWithM_, zipWithM, unless)
import Data.Foldable (Foldable(..))
import Data.Monoid (All(..), (<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier (Field)
import Insomnia.Types (Kind, TyVar)
import Insomnia.TypeDefn (TypeDefn (..),
                          ConstructorDef(..),
                          PrettyField(..),
                          canonicalizeConstructorDefs)

import Insomnia.Typecheck.Env

-- | Check that the two given type definitions for the given field are
-- equivalent.  For the purposes of error messages, the first
-- definition is treated as the one from a model, and the second is
-- from an ascribed model type.
equivTypeDefn :: Field -> TypeDefn -> TypeDefn -> TC ()
equivTypeDefn fld defn1 defn2 =
  case (defn1, defn2) of
    (EnumDefn n1, EnumDefn n2) ->
      unless (n1 == n2) $
      typeError ("enumeration type " <> formatErr fld
                 <> " defined with " <> formatErr n1
                 <> " inhabitants, but expected " <> formatErr n2)
    (DataDefn bnd1, DataDefn bnd2) ->
      U.lunbind2 bnd1 bnd2 $ \res ->
        case res of
          Nothing -> typeError ("data type "
                                <> formatErr (PrettyField fld defn1)
                                <> " has different number of type parameters than "
                                <> formatErr (PrettyField fld defn2))
          Just (kvs1, cdefs1_, kvs2, cdefs2_) -> do
            zipWithM_ (equivTypeParameter fld) kvs1 kvs2
            extendTyVarsCtx kvs1 $ do
              let
                cdefs1 = canonicalizeConstructorDefs cdefs1_
                cdefs2 = canonicalizeConstructorDefs cdefs2_
              unless (length cdefs1 == length cdefs2) $
                typeError ("data type definition "
                           <> formatErr (PrettyField fld defn1)
                           <> " has a different number of constructors than "
                           <> formatErr (PrettyField fld defn2))
              eqCs <- zipWithM equivConstructorDef cdefs1 cdefs2
              let
                allCsEq = getAll $ foldMap All eqCs
              unless allCsEq $
                typeError ("data type definiton "
                           <> formatErr (PrettyField fld defn1)
                           <> " has different constructors than "
                           <> formatErr (PrettyField fld defn2))
    _ -> typeError ("conflicting definitions "
                    <> formatErr (PrettyField fld defn1)
                    <> " and "
                    <> formatErr (PrettyField fld defn2))

equivTypeParameter :: Field
                      -> (TyVar, Kind)
                      -> (TyVar, Kind)
                      -> TC ()
equivTypeParameter fld (tv1, k1) (_, k2) =
  unless (k1 `U.aeq` k2) $
  typeError ("type parameter " <> formatErr tv1
             <> " of data type " <> formatErr fld
             <> " has kind " <> formatErr k1
             <> ", but expected " <> formatErr k2)

-- | Assumes that constructor defs are in a canonical order,
-- so if the names don't match, one of the data type definitions had
-- different constructors than the other one.
equivConstructorDef :: ConstructorDef -> ConstructorDef -> TC Bool
equivConstructorDef (ConstructorDef c1 args1) (ConstructorDef c2 args2) =
  return (c1 `U.aeq` c2 && args1 `U.aeq` args2)
