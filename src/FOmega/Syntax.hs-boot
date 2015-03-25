{-# LANGUAGE MultiParamTypeClasses #-}
module FOmega.Syntax where

import Insomnia.Pretty (Pretty)

data Field
data Kind
data Term
data Type
data Command

instance Pretty Kind
instance Pretty Type
instance Pretty Term
instance Pretty Command