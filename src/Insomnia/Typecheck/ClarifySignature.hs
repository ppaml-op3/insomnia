{-# LANGUAGE ViewPatterns #-}
module Insomnia.Typecheck.ClarifySignature (clarifySignature) where

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier (Path(..), Identifier, Field)
import Insomnia.Types (Kind(..), Type(..),
                       TyConName, TypeConstructor(..),
                       TypePath(..),
                       KindedTVar, kArrs)
import Insomnia.TypeDefn (TypeAlias(..), TypeDefn(..))
import Insomnia.ModelType (Signature(..), ModelType(..), TypeSigDecl(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SigOfModelType (signatureOfModelType)


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
clarifySignature pmod (SubmodelSig f bnd) =
  U.lunbind bnd $ \((ident, U.unembed -> modTy), rest) ->
  clarifySubmodel pmod f ident modTy rest

clarifyTypeSigDecl :: Path
                      -> Field
                      -> TyConName
                      -> TypeSigDecl
                      -> Signature
                      -> TC Signature
clarifyTypeSigDecl pmod f tycon tsd rest =
  case tsd of
   AliasTypeSigDecl {} -> do
     rest' <- clarifySignature pmod rest
     return $ TypeSig f $ U.bind (tycon, U.embed tsd) rest'
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
      in TypeAlias $ U.bind tvks ty
    mkTypeAlias' :: Kind -> Integer -> TypeConstructor -> ([KindedTVar], Type)
    mkTypeAlias' KType _ c = ([], TC c)
    mkTypeAlias' (KArr kdom kcod) n c =
      let tv = U.makeName "a" n
          (tvks, ty) = mkTypeAlias' kcod (n + 1) c
          tvks' = (tv,kdom) : tvks
          ty' = TApp ty (TV tv)
      in (tvks', ty')
    
clarifySubmodel :: Path
                   -> Field
                   -> Identifier
                   -> ModelType
                   -> Signature
                   -> TC Signature
clarifySubmodel pmod f ident subModTy rest = do
  subSig <- signatureOfModelType subModTy
  clearSubSig <- clarifySignature (ProjP pmod f) subSig
  rest' <- clarifySignature pmod rest
  return $ SubmodelSig f $ U.bind (ident, U.embed (SigMT clearSubSig)) rest'
