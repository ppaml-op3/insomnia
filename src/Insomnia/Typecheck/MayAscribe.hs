{-# LANGUAGE ViewPatterns, OverloadedStrings #-}
-- | Signature ascription.
module Insomnia.Typecheck.MayAscribe (mayAscribeV) where

import Control.Applicative ((<$>))
import Control.Lens
import Control.Monad (unless)
import Data.Monoid ((<>))
import Data.Foldable (traverse_)

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.ModuleKind
import Insomnia.Identifier (Identifier, Path(..), Field)
import Insomnia.Types (TypeConstructor(..), TypePath(..), TyConName,
                       Type, Kind(..))
import Insomnia.TypeDefn
import Insomnia.ModuleType (ModuleType, Signature(..), TypeSigDecl(..),
                            SigV(..), sigVKind, sigVSig)

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SigOfModuleType (signatureOfModuleType)
import Insomnia.Typecheck.ExtendModuleCtx (extendTypeSigDeclCtx, extendModuleCtxV)
import Insomnia.Typecheck.Selfify (selfifySigV )

import Insomnia.Typecheck.TypeDefn (checkTypeDefn, checkTypeAlias)
import Insomnia.Typecheck.Equiv.Types (equivTypes)
import Insomnia.Typecheck.Equiv.TypeDefn (equivTypeDefn)
import Insomnia.Typecheck.Equiv.TypeAlias (equivTypeAlias)

mayAscribeV :: SigV Signature -> SigV Signature -> TC (SigV Signature)
mayAscribeV sigv1 sigv2 =
  case (sigv1, sigv2) of
   (SigV msig1 ModelMK, SigV msig2 ModelMK) ->
     flip SigV ModelMK <$> mayAscribe msig1 msig2
   (SigV msig1 ModuleMK, SigV msig2 ModuleMK) ->
     flip SigV ModuleMK <$> mayAscribe msig1 msig2
   (SigV _ modK1, SigV _ modK2) ->
     typeError ("cannot ascribe a " <> formatErr modK2
                <> " type signature to a "
                <> formatErr modK1)

-- | TODO: @msig1 `mayAscribe` msig2@ succeeds if it is okay to
-- ascribe @msig2@ to any module whose type is @msig1@.  That is,
-- @msig2@ is more general than @msig1@.  Returns the second
-- signature.
mayAscribe :: Signature -> Signature -> TC Signature
mayAscribe msig1 msig2 = do
  modId <- U.lfresh (U.s2n "<unnamed module>")
  checkSignature (IdP modId) (TailPreSig msig1) msig2
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
  | TypePreSig Field TypeSigDecl PrefixedSignature
  | SubmodulePreSig Field (SigV Signature) PrefixedSignature


checkSigV :: Path -> PrefixedSignature -> SigV Signature -> TC ()
checkSigV pmod presig1 = traverse_ (checkSignature pmod presig1)


-- | @checkSignature pmod msig1 msig2@ checks that @msig2@ is less general
-- than @msig1@.
checkSignature :: Path -> PrefixedSignature -> Signature -> TC ()
checkSignature pmod msig1 msig2 =
  case msig2 of
    UnitSig -> return ()
    ValueSig fld ty mrest2 -> do
      checkValueField pmod fld ty msig1
      checkSignature pmod msig1 mrest2
    TypeSig fld bnd ->
      checkTypeField pmod fld bnd msig1 $ \msig1' mrest2 ->
      checkSignature pmod msig1' mrest2
    SubmoduleSig fld bnd ->
      checkSubmoduleField pmod fld bnd msig1 $ \msig1' mrest2 ->
      checkSignature pmod msig1' mrest2

checkValueField :: Path -> Field -> Type -> PrefixedSignature -> TC ()
checkValueField pmod fld ty msig1 =
  case msig1 of
    TailPreSig mrest1 -> checkValueFieldTail pmod fld ty mrest1
    ValuePreSig fld' ty' mrest1 ->
      matchValueField (fld,ty) (fld',ty') $ checkValueField pmod fld ty mrest1
    SubmodulePreSig _fld' _subSigV mrest1 ->
      checkValueField pmod fld ty mrest1
    TypePreSig _fld' _tsd1 mrest1 ->
      checkValueField pmod fld ty mrest1

-- | @matchValueField (fld2, ty2) (fld1, ty1) kNoMatch@ if the field
-- names match, checks that the types agree, if the fields don't match,
-- continues using the given continuation.
matchValueField :: (Field, Type)
                -> (Field, Type)
                -> TC ()
                -> TC ()
matchValueField (fld, ty) (fld', ty') kNoMatch =
  if fld == fld'
  then do
    same <- equivTypes ty ty' KType
    unless same $
      typeError ("value field " <> formatErr fld
                 <> " has type " <> formatErr ty'
                 <> " but signature requires " <> formatErr ty)
  else
    kNoMatch
        
checkValueFieldTail :: Path -> Field -> Type -> Signature -> TC ()
checkValueFieldTail pmod fld ty msig1 =
  case msig1 of
    UnitSig -> typeError ("signature specifies value field "
                          <> formatErr fld
                          <> ": " <> formatErr ty
                          <> "that is not present in the given structure")
    ValueSig fld' ty' mrest1 ->
      matchValueField (fld, ty) (fld', ty')
      $ checkValueFieldTail pmod fld ty mrest1
    SubmoduleSig fld' bnd ->
      U.lunbind bnd $ \((ident1, U.unembed -> moduleTy), mrest1_) -> do
        let pdefn = ProjP pmod fld'
            mrest1 = U.subst ident1 pdefn mrest1_
        subSigV <- signatureOfModuleType moduleTy
        subSelfV <- selfifySigV pdefn subSigV
        extendModuleCtxV subSelfV $
          checkValueFieldTail pmod fld ty mrest1
    TypeSig fld' bnd ->
      U.lunbind bnd $ \((tycon1, U.unembed -> tsd_), mrest1_) -> do
        let pdefn = TypePath pmod fld'
            dcon = TCGlobal pdefn
            tsd = U.subst tycon1 dcon tsd_
            mrest1 = U.subst tycon1 dcon mrest1_
        -- when matching in the rest of the signature, make use of
        -- provided type declaration.
        extendTypeSigDeclCtx dcon tsd $
          checkValueFieldTail pmod fld ty mrest1

checkTypeField :: Path
                  -> Field
                  -> U.Bind (TyConName, U.Embed TypeSigDecl) Signature
                  -> PrefixedSignature
                  -> (PrefixedSignature -> Signature -> TC a)
                  -> TC a
checkTypeField pmod fld bnd msig1 kont =
  case msig1 of
    TailPreSig mrest1 -> checkTypeFieldTail pmod fld bnd mrest1 kont
    ValuePreSig fld' ty' mrest1 ->
      checkTypeField pmod fld bnd mrest1 (kont . ValuePreSig fld' ty')
    SubmodulePreSig fld' subSigV mrest1 ->
      checkTypeField pmod fld bnd mrest1 (kont . SubmodulePreSig fld' subSigV)
    TypePreSig fld' tsd1 mrest1 ->
      if fld /= fld'
      then
        checkTypeField pmod fld bnd mrest1 $ \mrest1' ->
        kont (TypePreSig fld' tsd1 mrest1')
      else
        U.lunbind bnd $ \((tycon2, U.unembed -> tsd2_), mrest2_) -> do
          let
            -- substitute ident1 for ident2 in tsd2_ and in mrest2_
            -- such that tsd1 and tsd2 agree about the in scope type
            -- declaration.
            tsd2 = U.subst tycon2 (TCGlobal $ TypePath pmod fld) tsd2_
            mrest2 = U.subst tycon2 (TCGlobal $ TypePath pmod fld) mrest2_
          checkTypeSigDecl fld tsd1 tsd2
          kont (TypePreSig fld tsd1 mrest1) mrest2

checkTypeFieldTail :: Path
                      -> Field
                      -> U.Bind (TyConName, U.Embed TypeSigDecl) Signature
                      -> Signature
                      -> (PrefixedSignature -> Signature -> TC a)
                      -> TC a
checkTypeFieldTail pmod fld bnd msig1 kont =
  case msig1 of
    UnitSig -> 
      U.lunbind bnd $ \((_, _tsd), _) ->
      typeError ("signature specified type field "
                 <> formatErr fld
                 <> " as " <> formatErr (TypeSig fld bnd)
                 <> " that is not present in the given structure")
    ValueSig fld' ty' mrest1 ->
      checkTypeFieldTail pmod fld bnd mrest1 (kont . ValuePreSig fld' ty')
    SubmoduleSig fld' bnd' ->
      U.lunbind bnd' $ \((ident1, U.unembed -> moduleTy), mrest1_) -> do
        subSigV <- signatureOfModuleType moduleTy
        let pSubmod = ProjP pmod fld'
        selfSigV <- selfifySigV pSubmod subSigV
        let mrest1 = U.subst ident1 pSubmod mrest1_
        extendModuleCtxV selfSigV $
          checkTypeFieldTail pmod fld bnd mrest1 (kont . SubmodulePreSig fld' subSigV)
    TypeSig fld' bnd' ->
      if fld /= fld'
      then 
        U.lunbind bnd' $ \((tycon1, U.unembed -> tsd_), mrest1_) -> do
          let pdefn = TypePath pmod fld'
              dcon = TCGlobal pdefn
              tsd = U.subst tycon1 dcon tsd_
              mrest1 = U.subst tycon1 dcon mrest1_
          extendTypeSigDeclCtx dcon tsd $
            checkTypeFieldTail pmod fld bnd mrest1 $ \mrest1' ->
            kont (TypePreSig fld' tsd mrest1')
      else 
        U.lunbind2 bnd bnd' $ \res ->
        -- fields match.  give them the same identifier and check that
        -- the definition in tsd1 is more specific than the definition
        -- in tsd2.
        case res of
          Nothing -> fail ("checkTypeField internal error. "
                           <> " Did not expect lunbind2 to return Nothing")
          Just ((tycon2, U.unembed -> tsd2_), mrest2_,
                (tycon1, U.unembed -> tsd1_), mrest1_) -> do
            let pdefn = TypePath pmod fld'
                dcon = TCGlobal pdefn
                tsd1 = U.subst tycon1 dcon tsd1_
                tsd2 = U.subst tycon2 dcon tsd2_
                mrest1 = U.subst tycon1 dcon mrest1_
                mrest2 = U.subst tycon2 dcon mrest2_
            checkTypeSigDecl fld tsd1 tsd2
            extendTypeSigDeclCtx dcon tsd1 $
              kont (TypePreSig fld' tsd1 (TailPreSig mrest1)) mrest2
        
-- | @checkTypeSigDecl fld tsd1 tsd2@ checks that the type declaration
-- @tsd2@ is compatible with and is no more specific than @tsd1@.
checkTypeSigDecl :: Field
                    -> TypeSigDecl
                    -> TypeSigDecl
                    -> TC ()
checkTypeSigDecl fld tsd1 tsd2 =
  case tsd1 of
    AbstractTypeSigDecl k1 ->
      checkAbstractTypeDecl fld k1 tsd2
    ManifestTypeSigDecl defn1 ->
      checkManifestTypeDecl fld defn1 tsd2
    AliasTypeSigDecl alias ->
      checkAliasTypeDecl fld alias tsd2
      
-- | Given an abstract type in the more specific signature, check
-- that its corresponding declaration in the less specific signature is
-- also an abstract type of equivalent kind.
checkAbstractTypeDecl :: Field
                      -> Kind
                      -> TypeSigDecl
                      -> TC ()
checkAbstractTypeDecl fld k1 tsd2 =
  case tsd2 of
    AbstractTypeSigDecl k2 ->
      unless (k1 `U.aeq` k2) $
      typeError ("abstract type " <> formatErr fld
                 <> " has kind " <> formatErr k1
                 <> " but signature expects " <> formatErr k2)
    ManifestTypeSigDecl defn2 ->
      typeError ("abstract type " <> formatErr fld
                 <> " with kind " <> formatErr k1
                 <> " has been provided a definition in the signature "
                 <> formatErr (PrettyField fld defn2))
    AliasTypeSigDecl _alias2 ->
      error ("MayAscribe.checkAbstractTypeDecl: need to check that the alias expands to the same abstract type")

-- | Given a manifest type definition in the more specific signature, check
-- that its declaration in the less specific signature is either the same
-- manifest definition, or an abstract type of the correct kind.
checkManifestTypeDecl :: Field -> TypeDefn -> TypeSigDecl -> TC ()
checkManifestTypeDecl fld defn1 tsd2 =
  case tsd2 of
    AbstractTypeSigDecl k2 -> do
      (_, k1) <- checkTypeDefn (TCLocal $ U.s2n fld) defn1
      unless (k1 `U.aeq` k2) $
        typeError ("type declaration " <> formatErr (PrettyField fld defn1)
                   <> " has kind " <> formatErr k1
                   <> " but expected " <> formatErr k2)
    ManifestTypeSigDecl defn2 ->
      equivTypeDefn fld defn1 defn2
    AliasTypeSigDecl alias2 ->
      typeError ("module defining type declaration "
                 <> formatErr (PrettyField fld defn1)
                 <> " cannot be ascribed a type alias "
                 <> formatErr (PrettyField fld alias2))

-- | Given a type alias in the moder specific signature, check that
-- its declaration in the less specific signature is either an
-- abstract type with the same kind.
checkAliasTypeDecl :: Field -> TypeAlias -> TypeSigDecl -> TC ()
checkAliasTypeDecl fld alias1 tsd2 =
  case tsd2 of
    AbstractTypeSigDecl k2 -> do
      (_, aliasInfo) <- checkTypeAlias alias1
      let
        k1 = typeAliasInfoKind aliasInfo 
      unless (k1 `U.aeq` k2) $
        typeError ("The type alias " <> formatErr (PrettyField fld alias1)
                   <> "has kind " <> formatErr k1
                   <> " but expected " <> formatErr k2)
    ManifestTypeSigDecl defn2 ->
      typeError ("The module containing type alias "
                 <> formatErr (PrettyField fld alias1)
                 <> " cannot be ascribed a signature with type defined "
                 <> formatErr (PrettyField fld defn2))
    AliasTypeSigDecl alias2 ->
      equivTypeAlias fld alias1 alias2

checkSubmoduleField :: Path
                      -> Field
                      -> U.Bind (Identifier, U.Embed ModuleType) Signature
                      -> PrefixedSignature
                      -> (PrefixedSignature -> Signature -> TC a)
                      -> TC a
checkSubmoduleField pmod fld bnd msig1 kont =
  case msig1 of
    TailPreSig mrest1 -> checkSubmoduleFieldTail pmod fld bnd mrest1 kont
    ValuePreSig fld' ty' mrest1 ->
      checkSubmoduleField pmod fld bnd mrest1 (kont . ValuePreSig fld' ty')
    TypePreSig fld' tsd1 mrest1 ->
      checkSubmoduleField pmod fld bnd mrest1 (kont . TypePreSig fld' tsd1)
    SubmodulePreSig fld' sigV1 mrest1 ->
      if fld /= fld'
      then
        checkSubmoduleField pmod fld bnd mrest1 (kont . SubmodulePreSig fld' sigV1)
      else
        -- found a match.
        -- check that such a module can be ascribed the given signature.
        U.lunbind bnd $ \((ident2, U.unembed -> moduleTy2), mrest2_) -> do
          sigV2 <- signatureOfModuleType moduleTy2
          let
            pSubmod = ProjP pmod fld
            modK1 = sigV1 ^. sigVKind
            modK2 = sigV2 ^. sigVKind
          unless (modK1 == modK2) $
            typeError ("The sub-" <> formatErr modK1 <> " " <> formatErr pSubmod
                       <> " cannot be ascribed a "
                       <> formatErr modK1 <>" signature")
          checkSigV pSubmod (TailPreSig $ sigV1^.sigVSig) sigV2
          -- when mrest2 talks about this submodule, it should actually
          -- talk about the selfified version from sig1 which is just
          -- the projection of this submodule field from the current
          -- path.
          let mrest2 = U.subst ident2 pSubmod mrest2_
          kont (SubmodulePreSig fld' sigV1 mrest1) mrest2

checkSubmoduleFieldTail :: Path
                          -> Field
                          -> U.Bind (Identifier, U.Embed ModuleType) Signature
                          -> Signature
                          -> (PrefixedSignature -> Signature -> TC a)
                          -> TC a
checkSubmoduleFieldTail pmod fld bnd msig1 kont =
  case msig1 of
    UnitSig ->
      typeError ("signature specified a submodule "
                 <> formatErr fld
                 <> " that isn't present in the structure")
    ValueSig fld' ty' mrest1 ->
      checkSubmoduleFieldTail pmod fld bnd mrest1 (kont . ValuePreSig fld' ty')
    TypeSig fld' bnd' ->
      U.lunbind bnd' $ \((tycon, U.unembed -> tsd_), mrest1_) -> do
        let pdefn = TypePath pmod fld'
            dcon = TCGlobal pdefn
            tsd = U.subst tycon dcon tsd_
            mrest1 = U.subst tycon dcon mrest1_
        extendTypeSigDeclCtx dcon tsd $
          checkSubmoduleFieldTail pmod fld bnd mrest1 $ \mrest1' ->
          kont (TypePreSig fld' tsd mrest1')
    SubmoduleSig fld' bnd' ->
      {- module type M_SIG1 {
           module M :: { ... (1) }
           ... (3)
         }

         module type M_SIG2 {
           module M' :: { ... (2) }
           ... (4)
         }

         if M' is not M, then we want to add M to the environment
         (so we selfifiy it) and go on.

         if they coincide, then we want to make sure (1) and (2)
         refer to M using the same internal identifier (ie, we use
         lunbind2) and then check that signatures (1) and (2) match
         up.  then we extend the environment with the selfified M
         and go on checking (3) against (4).
      -}
      if fld /= fld'
      then U.lunbind bnd' $ \((ident1, U.unembed -> moduleTy1), mrest1_) -> do
        sigV1 <- signatureOfModuleType moduleTy1
        let pSubmod = ProjP pmod fld'
        selfSigV1 <- selfifySigV pSubmod sigV1
        let mrest1 = U.subst ident1 pSubmod mrest1_
        extendModuleCtxV selfSigV1 $
          checkSubmoduleFieldTail pmod fld bnd mrest1 $ \mrest1' ->
          kont (SubmodulePreSig fld' sigV1 mrest1')
      else U.lunbind2 bnd bnd' $ \res ->
      case res of
        Nothing -> fail ("checkSubmoduleField internal error. "
                         <> " Did not expect lunbind2 to return Nothing")
        Just ((ident2, U.unembed -> moduleTy2), mrest2_,
              (ident1, U.unembed -> moduleTy1), mrest1_) -> do
          (sigv1) <- signatureOfModuleType moduleTy1
          (sigv2) <- signatureOfModuleType moduleTy2
          let
            pSubmod = ProjP pmod fld
            modK1 = sigv1^.sigVKind
            modK2 = sigv2^.sigVKind
          unless (modK1 == modK2) $
            typeError ("The sub-" <> formatErr modK1 <> " " <> formatErr pSubmod
                       <> " cannot be ascribed a "
                       <> formatErr modK2 <>" signature")
          checkSigV pSubmod (TailPreSig $ sigv1 ^. sigVSig) sigv2
          selfSigV1 <- selfifySigV pSubmod sigv1
          let
            mrest1 = U.subst ident1 pSubmod mrest1_
            mrest2 = U.subst ident2 pSubmod mrest2_
          extendModuleCtxV selfSigV1 $
            kont (SubmodulePreSig fld' sigv1 (TailPreSig mrest1)) mrest2
