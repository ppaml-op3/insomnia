-- | Selfified signatures.
-- A selfified signature is like a non-dependent record kind.
-- All dependencies among type components of an ordinary signature
-- become paths:
--   Self(p; {t:K1,a. K2})
--     = {t : Self(p; K1),  Self(p; K2[p.t/a])}
module Insomnia.Typecheck.SelfSig where

import Insomnia.Identifier (Path)
import Insomnia.Types (Type, TypePath)
import Insomnia.Expr (QVar)
import Insomnia.ModuleType (TypeSigDecl, Signature)

-- | A selfified signature.  After selfification, all references to
-- declared types and values within the module are referenced
-- by their fully qualified name with respect to the path to the module.
data SelfSig =
  UnitSelfSig
  | ValueSelfSig QVar Type SelfSig
  | TypeSelfSig TypePath TypeSigDecl SelfSig
  | SubmoduleSelfSig Path SelfSig SelfSig
  | SubmodelSelfSig Path Signature SelfSig -- models aren't selfified

  

