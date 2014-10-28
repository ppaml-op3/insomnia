{-# LANGUAGE OverloadedStrings #-}
-- | Utitlities for checking type definitions
-- whether in a model type or in a model definition.
module Insomnia.Typecheck.TypeDefn (checkTypeDefn,
                                    checkTypeAlias,
                                    extendTypeDefnCtx,
                                    extendTypeAliasCtx
                                   ) where

import Control.Monad (forM, unless)
import Control.Monad.Reader.Class (MonadReader(..))

import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Types (Nat, Con, Kind(..), TyVar)
import Insomnia.TypeDefn

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkKind, checkType, inferType)

checkTypeDefn :: Con -> TypeDefn -> TC (TypeDefn, Kind)
checkTypeDefn dcon td =
  case td of
    DataDefn constrs -> checkDataDefn dcon constrs
    EnumDefn n -> checkEnumDefn dcon n

checkDataDefn :: Con -> DataDefn -> TC (TypeDefn, Kind)
checkDataDefn dcon bnd = do
  U.lunbind bnd $ \ (vks, constrs) -> do
    -- k1 -> k2 -> ... -> *
    let kparams = map snd vks
        cs = map (\(ConstructorDef c _) -> c) constrs
        algty = AlgType kparams cs
    mapM_ checkKind kparams
    constrs' <- extendDConCtx dcon (GenerativeTyCon $ AlgebraicType algty)
                $ extendTyVarsCtx vks $ forM constrs checkConstructor
    return (DataDefn $ U.bind vks constrs',
            foldr KArr KType (map snd vks))

checkEnumDefn :: Con -> Nat -> TC (TypeDefn, Kind)
checkEnumDefn dcon n = do
  unless (n > 0) $ do
    typeError ("when checking declaration of enumeration type "
               <> formatErr dcon
               <> " the number of elements "
               <> formatErr n <> "was negative")
  return (EnumDefn n, KType)


checkConstructor :: ConstructorDef -> TC ConstructorDef
checkConstructor (ConstructorDef ccon args) = do
  guardDuplicateCConDecl ccon
  args' <- forM args $ \arg -> checkType arg KType
  return (ConstructorDef ccon args')

-- | Extend the typing context by adding the given type defintion.
extendTypeDefnCtx :: Con -> TypeDefn -> TC a -> TC a
extendTypeDefnCtx dcon td =
  case td of
    DataDefn constrs -> extendDataDefnCtx dcon constrs
    EnumDefn n -> extendEnumDefnCtx dcon n

extendTypeAliasCtx :: Con -> TypeAlias -> TC a -> TC a
extendTypeAliasCtx dcon alias comp = do
  (alias', aliasInfo) <- checkTypeAlias alias
  env <- ask
  extendDConCtx dcon (AliasTyCon aliasInfo $ TypeAliasClosure env alias')
    $ comp

-- | Extend the typing context by adding the given type and value constructors
extendDataDefnCtx :: Con -> DataDefn -> TC a -> TC a
extendDataDefnCtx dcon bnd comp = do
  U.lunbind bnd $ \ (vks, constrs) -> do
    let kparams = map snd vks
        cs = map (\(ConstructorDef c _) -> c) constrs
        algty = AlgType kparams cs
    extendDConCtx dcon (GenerativeTyCon $ AlgebraicType algty) $ do
      let constructors = map (mkConstructor dcon vks) constrs
      extendConstructorsCtx constructors comp

-- | Extend the typing context by adding the given enumeration type
extendEnumDefnCtx :: Con -> Nat -> TC a -> TC a
extendEnumDefnCtx dcon n =
  extendDConCtx dcon (GenerativeTyCon $ EnumerationType n)

-- | @mkConstructor d vks (ConstructorDef c params)@ returns @(c,
-- ccon)@ where @ccon@ is a 'Constructor' for the type @d@ with the
-- given type and value parameters.
mkConstructor :: Con -> [(TyVar, Kind)] -> ConstructorDef -> (Con, AlgConstructor)
mkConstructor dcon vks (ConstructorDef ccon args) =
  (ccon, AlgConstructor (U.bind vks args) dcon)

-- | Check that the given type alias is well-formed.  Returns the
-- number of mandatory arguments to the type alias, and the kind of
-- the resulting type expression.
checkTypeAlias :: TypeAlias -> TC (TypeAlias, TypeAliasInfo)
checkTypeAlias (TypeAlias bnd) =
  U.lunbind bnd $ \(tvks, ty) -> do
    let kparams = map snd tvks
    mapM_ checkKind kparams
    (ty', kcod) <- extendTyVarsCtx tvks $ inferType ty
    return (TypeAlias (U.bind tvks ty')
            , TypeAliasInfo kparams kcod)
