{-# LANGUAGE FlexibleContexts, ViewPatterns, OverloadedStrings #-}
module Insomnia.Typecheck.ExtendModuleCtx (
  extendTypeSigDeclCtx
  , extendModuleCtxNF
  , extendModuleCtx
  , extendToplevelDeclCtx
  ) where

import Control.Lens
import Control.Monad.Reader.Class (MonadReader(..))

import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Types (TypeConstructor(..))
import Insomnia.Common.ModuleKind
import Insomnia.ModuleType (ToplevelSummary(..), TypeSigDecl(..), ModuleTypeNF(..), SigV(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig (SelfSig(..))
import Insomnia.Typecheck.Selfify (selfifySignature)
import Insomnia.Typecheck.TypeDefn (extendTypeDefnCtx, extendTypeAliasCtx)

extendTypeSigDeclCtx :: TypeConstructor -> TypeSigDecl -> TC a -> TC a
extendTypeSigDeclCtx dcon tsd = do
  case tsd of
    ManifestTypeSigDecl defn -> extendTypeDefnCtx dcon defn
    AbstractTypeSigDecl k ->
      extendDConCtx dcon (GenerativeTyCon $ AbstractType k)
    AliasTypeSigDecl alias -> extendTypeAliasCtx dcon alias

extendModuleCtxNF :: Path -> ModuleTypeNF -> TC a -> TC a
extendModuleCtxNF pmod mtnf =
  let
    extendModuleSig = case pmod of
      IdP modId -> extendModuleSigCtx modId mtnf
      _ -> id
    extendSelf = case mtnf of
      SigMTNF (SigV sig ModuleMK) -> \kont -> do
        selfSig <- selfifySignature pmod sig
        extendModuleCtx selfSig kont
      SigMTNF (SigV _ ModelMK) -> id
      FunMTNF {} -> id
  in
   extendModuleSig . extendSelf

-- | Add the datatypes of the given toplevel to the context with their
-- names selfified with respect to the given topref.
extendToplevelDeclCtx :: TopRef -> ToplevelSummary -> TC a -> TC a
extendToplevelDeclCtx _tr UnitTS kont = kont
extendToplevelDeclCtx tr (ModuleTS fld bnd) kont =
  U.lunbind bnd $ \((_modIdent, U.unembed -> mtnf), rest) ->
  extendModuleCtxNF (ProjP (TopRefP tr) fld) mtnf
  . extendToplevelDeclCtx tr rest
  $ kont
extendToplevelDeclCtx tr (SignatureTS fld bnd) kont =
  U.lunbind bnd $ \((sigId, _mtnf), rest_) ->
    let sigPath = SigTopRefP tr fld
        -- if the rest of the toplevel summary refers to this local sig, refer to it
        -- via the topref instead.
        rest = U.subst sigId sigPath rest_
    in extendToplevelDeclCtx tr rest kont

-- | Given a (selfified) signature, add all of its fields to the context
-- by prefixing them with the given path - presumably the path of this
-- very module.
extendModuleCtx :: SelfSig -> TC a -> TC a
extendModuleCtx UnitSelfSig = id
extendModuleCtx (ValueSelfSig qvar ty msig) =
  local (envGlobals . at qvar ?~ ty)
  . extendModuleCtx msig
extendModuleCtx (TypeSelfSig p tsd msig) =
  extendTypeSigDeclCtx (TCGlobal p) tsd
  . extendModuleCtx msig
extendModuleCtx (SubmoduleSelfSig _path subSig msig) =
  extendModuleCtx subSig
  . extendModuleCtx msig
extendModuleCtx (GenerativeSelfSig _path _subSig msig) =
  extendModuleCtx msig
