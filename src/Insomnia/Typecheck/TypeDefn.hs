{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
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

import Insomnia.Types (Nat, TypePath(..), TypeConstructor(..),
                       Kind(..), TyVar)
import Insomnia.TypeDefn

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkKind, checkType, inferType)

checkTypeDefn :: TypeConstructor -> TypeDefn -> TC (TypeDefn, Kind)
checkTypeDefn dcon td =
  case td of
    DataDefn constrs -> checkDataDefn dcon constrs
    EnumDefn n -> checkEnumDefn dcon n

checkDataDefn :: TypeConstructor -> DataDefn -> TC (TypeDefn, Kind)
checkDataDefn dcon bnd = do
  U.lunbind bnd $ \ (vks, constrs) -> do
    -- k1 -> k2 -> ... -> *
    let kparams = map snd vks
        cs = map (\(ConstructorDef c _) -> VCLocal c) constrs
        algty = AlgType kparams cs
    mapM_ checkKind kparams
    constrs' <- extendDConCtx dcon (GenerativeTyCon $ AlgebraicType algty)
                $ extendTyVarsCtx vks $ forM constrs checkConstructor
    return (DataDefn $ U.bind vks constrs',
            foldr KArr KType (map snd vks))

checkEnumDefn :: TypeConstructor -> Nat -> TC (TypeDefn, Kind)
checkEnumDefn dcon n = do
  unless (n > 0) $ do
    typeError ("when checking declaration of enumeration type "
               <> formatErr dcon
               <> " the number of elements "
               <> formatErr n <> "was negative")
  return (EnumDefn n, KType)


checkConstructor :: ConstructorDef -> TC ConstructorDef
checkConstructor (ConstructorDef ccon args) = do
  guardDuplicateCConDecl (VCLocal ccon)
  args' <- forM args $ \arg -> checkType arg KType
  return (ConstructorDef ccon args')

-- | Extend the typing context by adding the given type defintion.
extendTypeDefnCtx :: (U.LFresh m, MonadReader Env m)
                     => TypeConstructor -> TypeDefn -> m a -> m a
extendTypeDefnCtx dcon td kont = do
  (genTyCon, constructors) <- mkConstructors dcon td
  extendDConCtx dcon genTyCon
    $ extendConstructorsCtx constructors
    $ kont

extendTypeAliasCtx :: TypeConstructor -> TypeAlias -> TC a -> TC a
extendTypeAliasCtx dcon alias@(ManifestTypeAlias bnd) comp = do
  (alias', aliasInfo) <- checkTypeAlias alias
  env <- ask
  extendDConCtx dcon (AliasTyCon aliasInfo $ TypeAliasClosure env alias')
    $ comp
extendTypeAliasCtx dcon alias@(DataCopyTypeAlias tp defn) comp = do
  (alias', aliasInfo) <- checkTypeAlias alias
  -- if this alias is a datatype copy, also add the constructors to
  -- the env, o.w. nothing
  extCons <- do
    (_genTyCon, constructors) <- mkConstructors dcon defn
    return (extendConstructorsCtx constructors)
  env <- ask
  extendDConCtx dcon (AliasTyCon aliasInfo $ TypeAliasClosure env alias')
    $ extCons
    $ comp

-- | Given a type constructor and its definition, return the data type
-- descriptor, the value constructors, and the algebraic type
-- constructors to be added to the environment.
mkConstructors :: (U.LFresh m) => TypeConstructor -> TypeDefn -> m (TyConDesc, [(ValueConstructor, AlgConstructor)])
mkConstructors dcon td =
  case td of
   EnumDefn n -> return (GenerativeTyCon (EnumerationType n), [])
   DataDefn bnd ->
     U.lunbind bnd $ \ (vks, constrs) -> do
       let kparams = map snd vks
           makeVC = valueConstructorMakerForTypeConstructor dcon
           cs = map (\(ConstructorDef c _) -> makeVC c) constrs
           algty = AlgType kparams cs
           constructors = map (mkConstructor dcon vks) constrs
       return (GenerativeTyCon (AlgebraicType algty), constructors)


valueConstructorMakerForTypeConstructor :: TypeConstructor
                                           -> ValConName -> ValueConstructor
valueConstructorMakerForTypeConstructor tc =
  case tc of
   (TCGlobal tp) ->
     \name -> VCGlobal (Right $ InferredValConPath tp (U.name2String name))
   (TCLocal _) -> VCLocal

-- | @mkConstructor d vks (ConstructorDef c params)@ returns @(c,
-- ccon)@ where @ccon@ is a 'Constructor' for the type @d@ with the
-- given type and value parameters.
mkConstructor :: TypeConstructor -> [(TyVar, Kind)] -> ConstructorDef -> (ValueConstructor, AlgConstructor)
mkConstructor dcon vks (ConstructorDef ccon args) =
  let makeVC = valueConstructorMakerForTypeConstructor dcon
  in (makeVC ccon, AlgConstructor (U.bind vks args) dcon)

-- | Check that the given type alias is well-formed.  Returns the
-- number of mandatory arguments to the type alias, and the kind of
-- the resulting type expression.
checkTypeAlias :: TypeAlias -> TC (TypeAlias, TypeAliasInfo)
checkTypeAlias (ManifestTypeAlias bnd) =
  U.lunbind bnd $ \(tvks, ty) -> do
    let kparams = map snd tvks
    mapM_ checkKind kparams
    (ty', kcod) <- extendTyVarsCtx tvks $ inferType ty
    return (ManifestTypeAlias (U.bind tvks ty')
            , TypeAliasInfo kparams kcod)
checkTypeAlias (DataCopyTypeAlias tp defn) =
  -- XXX TODO: this is probably wrong for higher kinds.
  return (DataCopyTypeAlias tp defn
          , TypeAliasInfo [] KType)
