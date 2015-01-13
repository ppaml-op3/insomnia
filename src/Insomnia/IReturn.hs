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
import Insomnia.Module

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
valueDecl vd@(TabulatedSampleDecl {}) = vd

-- the rest are plumbing.

toplevel :: Toplevel -> Toplevel
toplevel (Toplevel items) = Toplevel $ map toplevelItem items

toplevelItem :: ToplevelItem -> ToplevelItem
toplevelItem t@(ToplevelModuleType {}) = t
toplevelItem (ToplevelModule ident me) = ToplevelModule ident (moduleExpr me)

moduleExpr :: ModuleExpr -> ModuleExpr
moduleExpr (ModuleStruct mdl) = ModuleStruct (module' mdl)
moduleExpr (ModuleModel mdl) = ModuleModel (modelExpr mdl)
moduleExpr (ModuleSeal me mt) = ModuleSeal (moduleExpr me) mt
moduleExpr me@(ModuleAssume {}) = me
moduleExpr me@(ModuleId {}) = me
moduleExpr m@(ModuleApp {}) = m -- p (p1, ..., pK) - there is nothing to recurse into

modelExpr :: ModelExpr -> ModelExpr
modelExpr (ModelStruct mdl) = ModelStruct (module' mdl)
modelExpr m@(ModelId {}) = m
modelExpr (ModelLocal m me mt) = ModelLocal (module' m) (modelExpr me) mt

module' :: Module -> Module
module' (Module ds) = Module (map decl ds)

decl :: Decl -> Decl
decl (ValueDecl f vd) = ValueDecl f (valueDecl vd)
decl (SubmoduleDefn f me) = SubmoduleDefn f (moduleExpr me)
decl (SampleModuleDefn f me) = SampleModuleDefn f (moduleExpr me)
decl d@(ImportDecl {}) = d
decl d@(TypeDefn {}) = d
decl d@(TypeAliasDefn {}) = d

