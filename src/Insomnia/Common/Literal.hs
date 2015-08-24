{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module Insomnia.Common.Literal where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless


data Literal = IntL !Integer
             | RealL !Double
             deriving (Show, Eq, Typeable, Generic)
                      
instance Alpha Literal
