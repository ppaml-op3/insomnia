module Insomnia.Typecheck.ConstructImportDefinitions (constructImportDefinitions) where

import Data.Monoid (Monoid(..), (<>), Endo(..))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Stochasticity
import Insomnia.Identifier (Path(..), lastOfPath)
import Insomnia.Expr (QVar(..), Expr(..))
import Insomnia.Types (TypeConstructor(..), Type(..), TypePath(..))
import Insomnia.TypeDefn (TypeAlias(..))
import Insomnia.ModuleType (TypeSigDecl(..))
import Insomnia.Module

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig

type Decls = Endo [Decl] 

singleDecl :: Decl -> Decls
singleDecl d = Endo (d:)

constructImportDefinitions :: SelfSig -> TC Decls
constructImportDefinitions (ValueSelfSig q ty rest) = do
  d <- importValue q ty
  ds <- constructImportDefinitions rest
  return (d <> ds)
constructImportDefinitions (TypeSelfSig tp tsd rest) = do
  d <- importType tp tsd
  ds <- constructImportDefinitions rest
  return (d <> ds)
constructImportDefinitions (SubmoduleSelfSig p _ rest) = do
  d <- importSubmodule p
  ds <- constructImportDefinitions rest
  return (d <> ds)
constructImportDefinitions (GenerativeSelfSig p _ rest) = do
  d <- importSubmodule p
  ds <- constructImportDefinitions rest
  return (d <> ds)
constructImportDefinitions UnitSelfSig = return mempty

importSubmodule :: Path -> TC Decls
importSubmodule pSub = do
  let f = lastOfPath pSub
  return $ singleDecl $ SubmoduleDefn f (ModuleId pSub)

importValue :: QVar -> Type -> TC Decls
importValue q@(QVar _ f) ty = do
  let
    -- sig f : T
    -- val f = p.f
    dSig = singleDecl $ ValueDecl f $ SigDecl DeterministicParam ty
    dVal = singleDecl $ ValueDecl f $ ValDecl (Q q)
  return (dSig <> dVal)

importType :: TypePath -> TypeSigDecl -> TC Decls
importType tp@(TypePath _ f) _tsd = do
  -- TODO: import constructors
  -- TODO: for polymorphic types this doesn't kindcheck.
  return $ singleDecl $ TypeAliasDefn f $ TypeAlias $ U.bind [] (TC (TCGlobal tp))
   
