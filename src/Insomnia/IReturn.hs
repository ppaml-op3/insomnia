-- | Insert 'return' statements in random variable definitions.
-- That is, change
--
-- @
--   val x = e
-- @
--
-- into
--
-- @
--   val x ~ return e
-- @
module Insomnia.IReturn where

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Expr
import Insomnia.Toplevel
import Insomnia.Model

-- this is the meat of the transformation.

expr :: Expr -> Expr
expr (Let bnd) =
  let (b, e) = UU.unsafeUnbind bnd
      e' = expr e
  in Let (U.bind b e')
expr e = Return e

valueDecl :: ValueDecl -> ValueDecl
valueDecl (ValDecl e) = SampleDecl (expr e)
valueDecl vd@(FunDecl {}) = vd
valueDecl vd@(SampleDecl {}) = vd
valueDecl vd@(SigDecl {}) = vd
valueDecl vd@(ParameterDecl {}) = vd

-- the rest are plumbing.

toplevel :: Toplevel -> Toplevel
toplevel (Toplevel items) = Toplevel $ map toplevelItem items

toplevelItem :: ToplevelItem -> ToplevelItem
toplevelItem t@(ToplevelModelType {}) = t
toplevelItem (ToplevelModel ident me) = ToplevelModel ident (modelExpr me)

modelExpr :: ModelExpr -> ModelExpr
modelExpr (ModelStruct mdl) = ModelStruct (model mdl)
modelExpr me = me

model :: Model -> Model
model (Model ds) = Model (map decl ds)

decl :: Decl -> Decl
decl (ValueDecl f vd) = ValueDecl f (valueDecl vd)
decl (SubmodelDefn f me) = SubmodelDefn f (modelExpr me)
decl d = d

