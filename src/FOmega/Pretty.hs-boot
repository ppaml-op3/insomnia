module FOmega.Pretty where

import Text.PrettyPrint (Doc)
import Insomnia.Pretty (PM)
import {-# SOURCE #-} FOmega.Syntax (Kind, Type, Term)


ppKind :: Kind -> PM Doc
ppType :: Type -> PM Doc
ppTerm :: Term -> PM Doc

