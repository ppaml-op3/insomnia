{-# LANGUAGE ViewPatterns, OverloadedStrings #-}
-- | Signature ascription.
module Insomnia.Typecheck.MayAscribe (mayAscribe) where

import Control.Monad (unless)
import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier (Identifier, Path(..), Field)
import Insomnia.Types (Con(..), Type, Kind)
import Insomnia.TypeDefn
import Insomnia.ModelType (Signature(..), TypeSigDecl(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.ModelType (extendTypeSigDeclCtx)

import Insomnia.Typecheck.TypeDefn (checkTypeDefn)
import Insomnia.Typecheck.Equiv.TypeDefn (equivTypeDefn)

-- | TODO: @msig1 `mayAscribe` msig2@ succeeds if it is okay to
-- ascribe @msig2@ to any model whose type is @msig1@.  That is,
-- @msig2@ is more general than @msig1@.  Returns the second
-- signature.
mayAscribe :: Signature -> Signature -> TC Signature
mayAscribe msig1 msig2 = do
  checkSignature (TailPreSig msig1) msig2
  return msig2

-- | The signature matching algorithm is essentially O(n^2) in the
-- number of signature components, because we repeatedly scan the more
-- specific signature (msig1) looking for the components of the less
-- specific one (msig2) .  One complication that comes up is that
-- because of type dependencies, we must enrich the environment with
-- the components of msig1 as we traverse msig2.  When it comes to
-- type definitions, that presents the question of whether we should
-- add the definition to the context or not.  It turns out that that
-- depends on whether we already matched some prefix of msig1.  On the
-- other hand, we can't just continue from the place in msig1 where we
-- left off, because of perverse signatures such as: 'M_SIG1 = sig
-- type w type z = w end' matching against 'M_SIG2 = sig type z type w
-- = z end'.  We must must look at M_SIG1 from the beginning when
-- matching each of M_SIG2's z and w, but we mustn't add M_SIG1's w
-- and z to the typing context more than once.  The solution is to
-- convert the part of M_SIG1 that we've already seen into a
-- PrefixedSignature in the continuation.  The continuation can then
-- know that whatever definition we come across has already been added
-- to the typing context.  In particular note the contrast between
-- TypePreSig and TypeSig.  The latter binds the newly declared type in
-- the rest of the signature, while the former doesn't.
data PrefixedSignature
  = TailPreSig Signature
  | ValuePreSig Field Type PrefixedSignature
  | TypePreSig Field Identifier TypeSigDecl PrefixedSignature


-- | @checkSignature msig1 msig2@ checks that @msig2@ is less general
-- than @msig1@.
checkSignature :: PrefixedSignature -> Signature -> TC ()
checkSignature msig1 msig2 =
  case msig2 of
    UnitSig -> return ()
    ValueSig fld ty mrest2 -> do
      checkValueField fld ty msig1
      checkSignature msig1 mrest2
    TypeSig fld bnd ->
      checkTypeField fld bnd msig1 $ \msig1' mrest2 ->
      checkSignature msig1' mrest2


checkValueField :: Field -> Type -> PrefixedSignature -> TC ()
checkValueField fld ty msig1 =
  case msig1 of
    TailPreSig mrest1 -> checkValueFieldTail fld ty mrest1
    ValuePreSig fld' ty' mrest1 ->
      matchValueField (fld,ty) (fld',ty') $ checkValueField fld ty mrest1
    TypePreSig _fld' _ident1 _tsd1 mrest1 ->
      checkValueField fld ty mrest1

-- | @matchValueField (fld2, ty2) (fld1, ty1) kNoMatch@ if the field
-- names match, checks that the types agree, if the fields don't match,
-- continues using the given continuation.
matchValueField :: (Field, Type)
                -> (Field, Type)
                -> TC ()
                -> TC ()
matchValueField (fld, ty) (fld', ty') kNoMatch =
  if fld == fld'
  then
    unless (ty `U.aeq` ty') $ do
      typeError ("value field " <> formatErr fld
                 <> " has type " <> formatErr ty'
                 <> " but signature requires " <> formatErr ty)
  else
    kNoMatch
        
checkValueFieldTail :: Field -> Type -> Signature -> TC ()
checkValueFieldTail fld ty msig1 =
  case msig1 of
    UnitSig -> typeError ("signature specifies value field "
                          <> formatErr fld
                          <> ": " <> formatErr ty
                          <> "that is not present in the given structure")
    ValueSig fld' ty' mrest1 ->
      matchValueField (fld, ty) (fld', ty') $ checkValueFieldTail fld ty mrest1
    TypeSig _fld' bnd ->
      U.lunbind bnd $ \((ident1, U.unembed -> tsd), mrest1) -> do
        let dcon = Con (IdP ident1)
        -- when matching in the rest of the signature, make use of
        -- provided type declaration.
        extendTypeSigDeclCtx dcon tsd $
          checkValueFieldTail fld ty mrest1

checkTypeField :: Field
                  -> U.Bind (Identifier, U.Embed TypeSigDecl) Signature
                  -> PrefixedSignature
                  -> (PrefixedSignature -> Signature -> TC a)
                  -> TC a
checkTypeField fld bnd msig1 kont =
  case msig1 of
    TailPreSig mrest1 -> checkTypeFieldTail fld bnd mrest1 kont
    ValuePreSig fld' ty' mrest1 ->
      checkTypeField fld bnd mrest1 (kont . ValuePreSig fld' ty')
    TypePreSig fld' ident1 tsd1 mrest1 ->
      if fld /= fld'
      then
        checkTypeField fld bnd mrest1 $ \mrest1' ->
        kont (TypePreSig fld' ident1 tsd1 mrest1')
      else
        U.lunbind bnd $ \((ident2, U.unembed -> tsd2_), mrest2_) -> do
          let
            -- substitute ident2 for ident1 in tsd2_ and in mrest2_
            -- such that tsd1 and tsd2 agree about the in scope type
            -- declaration.
            tsd2 = U.subst ident2 (IdP ident1) tsd2_
            mrest2 = U.subst ident2 (IdP ident1) mrest2_
          checkTypeSigDecl fld tsd1 tsd2
          kont (TypePreSig fld' ident1 tsd1 mrest1) mrest2

checkTypeFieldTail :: Field
                  -> U.Bind (Identifier, U.Embed TypeSigDecl) Signature
                  -> Signature
                  -> (PrefixedSignature -> Signature -> TC a)
                  -> TC a
checkTypeFieldTail fld bnd msig1 kont =
  case msig1 of
    UnitSig -> 
      U.lunbind bnd $ \((_, _tsd), _) ->
      typeError ("signature specified type field "
                 <> formatErr fld
                 <> " as " <> formatErr (TypeSig fld bnd)
                 <> " that is not present in the given structure")
    ValueSig fld' ty' mrest1 ->
      checkTypeFieldTail fld bnd mrest1 (kont . ValuePreSig fld' ty')
    TypeSig fld' bnd' ->
      if fld /= fld'
      then 
        U.lunbind bnd' $ \((ident1, U.unembed -> tsd), mrest1) -> do
          let dcon = Con (IdP ident1)
          extendTypeSigDeclCtx dcon tsd $
            checkTypeFieldTail fld bnd mrest1 $ \mrest1' ->
            kont (TypePreSig fld' ident1 tsd mrest1')
      else 
        U.lunbind2 bnd bnd' $ \res ->
        -- fields match.  give them the same identifier and check that
        -- the definition in tsd1 is more specific than the definition
        -- in tsd2.
        case res of
          Nothing -> fail ("checkTypeField internal error. "
                           <> " Did not expect lunbind2 to return Nothing")
          Just ((_ident2, U.unembed -> tsd2), mrest2,
                (ident1, U.unembed -> tsd1), mrest1) -> do
            checkTypeSigDecl fld tsd1 tsd2
            let dcon1 = Con (IdP ident1)
            extendTypeSigDeclCtx dcon1 tsd1 $
              kont (TypePreSig fld' ident1 tsd1 (TailPreSig mrest1)) mrest2
        
-- | TODO: @checkTypeSigDecl fld tsd1 tsd2@ checks that the type declaration
-- @tsd2@ is compatible with and is no more specific than @tsd1@.
checkTypeSigDecl :: Field
                    -> TypeSigDecl
                    -> TypeSigDecl
                    -> TC ()
checkTypeSigDecl fld tsd1 tsd2 =
  case tsd1 of
    TypeSigDecl (Just k1) Nothing ->
      checkAbstractTypeDecl fld k1 tsd2
    TypeSigDecl Nothing (Just defn1) ->
      checkManifestTypeDecl fld defn1 tsd2
    _ -> error "MayAscribe.checkTypeSigDecl: internal error - either a kind or a definition should be specified"

-- | Given an abstract type in the more specific signature, check
-- that its corresponding declaration in the less specific signature is
-- also an abstract type of equivalent kind.
checkAbstractTypeDecl :: Field
                      -> Kind
                      -> TypeSigDecl
                      -> TC ()
checkAbstractTypeDecl fld k1 tsd2 =
  case tsd2 of
    TypeSigDecl (Just k2) Nothing ->
      unless (k1 `U.aeq` k2) $
      typeError ("abstract type " <> formatErr fld
                 <> " has kind " <> formatErr k1
                 <> " but signature expects " <> formatErr k2)
    TypeSigDecl Nothing (Just defn2) ->
      typeError ("abstract type " <> formatErr fld
                 <> " with kind " <> formatErr k1
                 <> " has been provided a definition in the signature "
                 <> formatErr (PrettyTypeDefn fld defn2))
    _ -> error "MayAscribe.checkAbstractTypeDecl : internal error - either a kind or a definition should be specified"

-- | Given a manifest type definition in the more specific signature, check
-- that its declaration in the less specific signature is either the same
-- manifest definition, or an abstract type of the correct kind.
checkManifestTypeDecl :: Field -> TypeDefn -> TypeSigDecl -> TC ()
checkManifestTypeDecl fld defn1 tsd2 =
  case tsd2 of
    TypeSigDecl (Just k2) Nothing -> do
      (_, k1) <- checkTypeDefn (Con $ IdP $ U.s2n fld) defn1
      unless (k1 `U.aeq` k2) $
        typeError ("type declaration " <> formatErr (PrettyTypeDefn fld defn1)
                   <> " has kind " <> formatErr k1
                   <> " but expected " <> formatErr k2)
    TypeSigDecl Nothing (Just defn2) ->
      equivTypeDefn fld defn1 defn2
    _ -> error "MayAscribe.checkManifestTypeDecl : internal error - either a kind of a definition should be specified"

