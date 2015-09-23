import "examples/Prelude.ism" (module Prelude)
import "examples/DataTypes.ism" (module DataTypes)

OBS = module type {
  sig x : Prelude.Bool
}

FLIP = model type {
  sig flip_prior : Real
  Kernel : model type {
    sig x : Prelude.Bool
  }
}

Flip : FLIP = model {
  val flip_prior ~ Prelude.uniform { lo = 0.0, hi = 1.0 }
  Kernel = model {
    val x ~ Prelude.flip flip_prior
  }
}

Obs = module {
  val x = Prelude.True
}

M = module {
  type ListObs = DataTypes.List Prelude.Bool

  val myflips = DataTypes.Cons Prelude.True (DataTypes.Cons Prelude.False DataTypes.Nil)


  -- build a packed model from a list of observations
  sig h : DataTypes.List Prelude.Bool -> {{ FLIP }}
  fun h ys = case ys of
    DataTypes.Nil -> pack {{ Flip }} as FLIP
    (DataTypes.Cons y ys2) -> let
      mrest = h ys2
      in pack {{ observe (unpack {{ mrest }} as FLIP) where Kernel is module { val x = y} }} as FLIP
  
  -- the resulting model that learned the flip values
  It = unpack {{ h myflips }} as FLIP

}
