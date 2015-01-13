{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      FlexibleContexts, MultiParamTypeClasses,
      TemplateHaskell
  #-}
module Insomnia.ModuleType where

import Control.Applicative
import Control.Lens
import Data.Foldable (Foldable(..))
import Data.Traversable (foldMapDefault, fmapDefault)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.Expr (Expr)
import Insomnia.TypeDefn

import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope

data ModuleType =
  SigMT !(SigV Signature) -- "module/model { decls ... }"
  | IdentMT !SigIdentifier -- "X_SIG"
  | FunMT !(Bind (Telescope (FunctorArgument ModuleType)) ModuleType)
  deriving (Show, Typeable, Generic)

data FunctorArgument t =
  FunctorArgument !Identifier !(Embed ModuleKind) !(Embed t)
  deriving (Show, Typeable, Generic)

data Signature =
  UnitSig
  | ValueSig !Field !Type !Signature
  | TypeSig !Field !(Bind (TyConName, Embed TypeSigDecl) Signature)
  | SubmoduleSig !Field !(Bind (Identifier, Embed ModuleType) Signature)
    deriving (Show, Typeable, Generic)

-- module type normal form: all signature identifiers have been resolved.
data ModuleTypeNF =
  SigMTNF (SigV Signature)
  | FunMTNF !(Bind (Telescope (FunctorArgument ModuleTypeNF)) ModuleTypeNF)
    deriving (Show, Typeable, Generic)

-- | After evaluating a ModuleType, we get a signature together with its kind.
-- (the datatype is parametrized because we'll also use it for SelfSig during typechecking)
data SigV a = SigV { _sigVSig :: !a
                   , _sigVKind :: !ModuleKind
                   }
                deriving (Show, Typeable, Generic)

-- | A type declaration in a signature.
-- This should really be @Either Kind TypeDefn@ or perhaps
-- @Either Kind (Kind, TypeDefn)@, but we will separate them, for now.
-- The invariant, however, is that both Maybes can't be Nothing.
data TypeSigDecl =
  AbstractTypeSigDecl !Kind
  | ManifestTypeSigDecl !TypeDefn
  | AliasTypeSigDecl !TypeAlias
  deriving (Show, Typeable, Generic)

$(makeLenses ''SigV)

instance Functor FunctorArgument where
  fmap = fmapDefault

instance Foldable FunctorArgument where
  foldMap = foldMapDefault

instance Traversable FunctorArgument where
  traverse f (FunctorArgument x modK (Embed t)) = (FunctorArgument x modK . Embed) <$> f t

moduleTypeNormalFormEmbed :: ModuleTypeNF -> ModuleType
moduleTypeNormalFormEmbed (SigMTNF s) = SigMT s
moduleTypeNormalFormEmbed (FunMTNF bnd) =
  let (args, body) = UU.unsafeUnbind bnd
      args' = fmapTelescope (fmap moduleTypeNormalFormEmbed) args
      body' = moduleTypeNormalFormEmbed body
  in FunMT $ bind args' body'

instance Traversable SigV where
  traverse = sigVSig

instance Foldable SigV where
  foldMap = foldMapDefault

instance Functor SigV where
  fmap = fmapDefault

instance Alpha ModuleType
instance Alpha Signature
instance Alpha a => Alpha (FunctorArgument a)
instance Alpha a => Alpha (SigV a)
instance Alpha TypeSigDecl
instance Alpha ModuleTypeNF

instance Subst Path Signature
instance Subst Path TypeSigDecl
instance Subst Path ModuleType
instance Subst Path a => Subst Path (SigV a)
instance Subst Path a => Subst Path (FunctorArgument a)
instance Subst Path ModuleTypeNF

instance Subst ValueConstructor ModuleType
instance Subst ValueConstructor Signature
instance Subst ValueConstructor a => Subst ValueConstructor (FunctorArgument a)
instance Subst ValueConstructor TypeSigDecl
instance Subst ValueConstructor a => Subst ValueConstructor (SigV a)

instance Subst TypeConstructor ModuleType
instance Subst TypeConstructor Signature
instance Subst TypeConstructor a => Subst TypeConstructor (FunctorArgument a)
instance Subst TypeConstructor TypeSigDecl
instance Subst TypeConstructor a => Subst TypeConstructor (SigV a)

-- model types do not have expressions in them.
instance Subst Expr ModuleType where
  subst _ _ = id
  substs _ = id
