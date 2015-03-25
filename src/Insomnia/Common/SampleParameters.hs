{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, TemplateHaskell #-}
module Insomnia.Common.SampleParameters where

import Control.Lens
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless (Alpha)

data UseDefault = UseDefault
                  deriving (Show, Eq, Typeable, Generic)

data SampleParameters = SampleParameters {
  _numSamplesParameter :: !Int
  , _numBurninParameter :: !(Either UseDefault Int)
  }
                        deriving (Show, Eq, Typeable, Generic)

$(makeLenses ''SampleParameters)

instance Alpha UseDefault
instance Alpha SampleParameters

useDefault :: Either UseDefault a
useDefault = Left UseDefault

_NonDefault :: Prism (Either UseDefault a) (Either UseDefault b) a b
_NonDefault = prism Right (\e ->
                            case e of
                             Left UseDefault -> Left (Left UseDefault)
                             Right x -> Right x)
