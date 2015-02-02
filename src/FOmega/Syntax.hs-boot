{-# LANGUAGE MultiParamTypeClasses #-}
module FOmega.Syntax where

import Insomnia.Pretty (Pretty)

data Field
data Kind
data Term
data Type

instance Pretty Kind
instance Pretty Type
instance Pretty Term
