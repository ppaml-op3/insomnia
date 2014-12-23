module Insomnia.Typecheck.SigOfModuleType where

import Insomnia.ModuleType (ModuleType(..), Signature, SigV)

import Insomnia.Typecheck.Env


signatureOfModuleType :: ModuleType -> TC (SigV Signature)
signatureOfModuleType (SigMT sigv) = return sigv
signatureOfModuleType (IdentMT msigId) = lookupModuleType msigId
