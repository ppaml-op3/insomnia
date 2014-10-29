module Insomnia.Typecheck.SigOfModelType where

import Insomnia.ModelType (ModelType(..), Signature)

import Insomnia.Typecheck.Env


signatureOfModelType :: ModelType -> TC Signature
signatureOfModelType (SigMT sig) = return sig
signatureOfModelType (IdentMT msigId) = lookupModelType msigId
