{-# LANGUAGE DeriveGeneric,
      DeriveDataTypeable,
      MultiParamTypeClasses
  #-}
module Insomnia.Query where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless (Alpha, Subst(..))

import Insomnia.Identifier (Path)
import Insomnia.Common.SampleParameters

data QueryExpr = GenSamplesQE !Path !SampleParameters
                 deriving (Show, Eq, Typeable, Generic)

instance Alpha QueryExpr

instance Subst Path QueryExpr

