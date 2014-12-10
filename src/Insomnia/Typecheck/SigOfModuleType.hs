module Insomnia.Typecheck.SigOfModuleType where

import Insomnia.Common.ModuleKind
import Insomnia.ModuleType (ModuleType(..), Signature)

import Insomnia.Typecheck.Env


signatureOfModuleType :: ModuleType -> TC (Signature, ModuleKind)
signatureOfModuleType (SigMT sig mk) = return (sig, mk)
signatureOfModuleType (IdentMT msigId) = lookupModuleType msigId
