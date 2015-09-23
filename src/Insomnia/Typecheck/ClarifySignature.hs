{-# LANGUAGE ViewPatterns, OverloadedStrings #-}
module Insomnia.Typecheck.ClarifySignature (clarifySignatureV, clarifySignatureNF) where

import Control.Applicative

import Data.Monoid((<>))

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Common.ModuleKind
import Insomnia.Identifier (Path(..), Identifier, Field)
import Insomnia.Types (Kind(..), Type(..),
                       TyConName, TypeConstructor(..),
                       TypePath(..),
                       KindedTVar, kArrs)
import Insomnia.TypeDefn (TypeAlias(..), TypeDefn(..))
import Insomnia.ModuleType (Signature(..), ModuleType(..),
                            ModuleTypeNF(..),
                            TypeSigDecl(..), SigV(..),
                            moduleTypeNormalFormEmbed)

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.WhnfModuleType (whnfModuleType)


-- | Clarify a signature by making its abstract types be manifestly equal to
-- the projections from the corresponding fields of the given module
-- path.  But note that for /model/-types and functor signatures we do
-- not do this: a model signature does not refer to a module until it
-- has been sampled, nor a functor until it is applied.
clarifySignatureNF :: Path -> ModuleTypeNF -> TC ModuleTypeNF
clarifySignatureNF pmod (SigMTNF s) = SigMTNF <$> clarifySignatureV pmod s
clarifySignatureNF _pmod fn@(FunMTNF {}) = return fn

clarifySignatureV :: Path -> SigV Signature -> TC (SigV Signature)
clarifySignatureV pmod (SigV msig ModuleMK) = do
  clearSig <- clarifySignature pmod msig
  return (SigV clearSig ModuleMK)
clarifySignatureV _pmod s@(SigV _ ModelMK) = return s

-- | Given the signature of the given path (ie, assume that the module
-- with that path has the given signature), return a signature that's
-- been made partly transluscent by equating all its type components
-- (and the types of its submodule components...) to the corresponding
-- components of the given path.
--
-- Examples:
--   clarifySignature X.Y { type t = t' ; ... }    = { type t = t' ; ... }
--   clarifySignature X.Y { type t :: k ; ... }    = { type t = X.Y.t ; ... }
--   clarifySignature X.Y { module M :: { decls } ; ... } = { module M :: clarifySignature X.Y.M { decls } ; ... }
--
-- TODO: share the value constructors of a generative type definition.
-- The purpose of clarifying a signature is for code like:
--
--   model Z { data IntList = Nil | Cons ... }
--   model Y = Z
--
-- here it should be the case that Y.IntList and Z.IntList are the
-- same data type, and Y.Cons and Z.Cons are interchangeable.
clarifySignature :: Path -> Signature -> TC Signature
clarifySignature _pmod UnitSig = return UnitSig
clarifySignature pmod (ValueSig f ty rest) = do
  rest' <- clarifySignature pmod rest
  return $ ValueSig f ty rest'
clarifySignature pmod (TypeSig f bnd) =
  U.lunbind bnd $ \((tycon, U.unembed -> tsd), rest) ->
  clarifyTypeSigDecl pmod f tycon tsd rest
clarifySignature pmod (SubmoduleSig f bnd) =
  U.lunbind bnd $ \((ident, U.unembed -> modTy), rest) ->
  clarifySubmodule pmod f ident modTy rest

clarifyTypeSigDecl :: Path
                      -> Field
                      -> TyConName
                      -> TypeSigDecl
                      -> Signature
                      -> TC Signature
clarifyTypeSigDecl pmod f tycon tsd rest =
  case tsd of
   AliasTypeSigDecl (ManifestTypeAlias _clz) -> do
     rest' <- clarifySignature pmod rest
     return $ TypeSig f $ U.bind (tycon, U.embed tsd) rest'
   AliasTypeSigDecl (DataCopyTypeAlias _tp _defn) ->
     typeError ("clarifyTypeSigDecl unimplemented for data type copies")
   AbstractTypeSigDecl k -> do
     let c = TCGlobal (TypePath pmod f)
         a = mkTypeAlias k c
     rest' <- clarifySignature pmod rest
     return $ TypeSig f $ U.bind (tycon, U.embed $ AliasTypeSigDecl a) rest'
   ManifestTypeSigDecl defn -> do
     let c = TCGlobal (TypePath pmod f)
         a = mkTypeAlias (defnKind defn) c
     -- TODO: also need to alias the value constructors.  Will need a
     -- new AST node...
     rest' <- clarifySignature pmod rest
     return $ TypeSig f $ U.bind (tycon, U.embed $ AliasTypeSigDecl a) rest'
  where
    defnKind (DataDefn bnd) =
      let (tvks, _) = UU.unsafeUnbind bnd
          ks = map snd tvks
      in ks `kArrs` KType
    defnKind (EnumDefn _) = KType

    -- | given type X.Y.T of kind k1 -> ... -> kN -> KType
    -- construct the type alias
    --    type Alias a0 .... aN = X.Y.T a0 ... aN
    mkTypeAlias :: Kind -> TypeConstructor -> TypeAlias
    mkTypeAlias k c =
      let (tvks, ty) = mkTypeAlias' k 0 c
      in ManifestTypeAlias (U.bind tvks ty)
    mkTypeAlias' :: Kind -> Integer -> TypeConstructor -> ([KindedTVar], Type)
    mkTypeAlias' KType _ c = ([], TC c)
    mkTypeAlias' (KArr kdom kcod) n c =
      let tv = U.makeName "a" n
          (tvks, ty) = mkTypeAlias' kcod (n + 1) c
          tvks' = (tv,kdom) : tvks
          ty' = TApp ty (TV tv)
      in (tvks', ty')

clarifySubmodule :: Path
                   -> Field
                   -> Identifier
                   -> ModuleType
                   -> Signature
                   -> TC Signature
clarifySubmodule pmod f ident subModTy rest = do
  subSigNF <- whnfModuleType subModTy
              <??@ ("while clarifying submodule " <> formatErr pmod)
  clearSubSigNF <- clarifySignatureNF (ProjP pmod f) subSigNF
  rest' <- clarifySignature pmod rest
  return $ SubmoduleSig f $ U.bind (ident, U.embed (moduleTypeNormalFormEmbed clearSubSigNF)) rest'
