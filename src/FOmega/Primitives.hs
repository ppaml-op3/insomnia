module FOmega.Primitives where

import Data.Monoid (mconcat)
import qualified Data.Map as M
import qualified Unbound.Generics.LocallyNameless as U

import FOmega.Syntax (Var)
import FOmega.Value

primitives :: M.Map Var Value
primitives =
  mkTable [ primitive "__BOOT.intAdd" 0 2
          , primitive "__BOOT.ifIntLt" 1 4
          , primitive "__BOOT.Distribution.choose" 1 3
          , primitive "__BOOT.Distribution.uniform" 0 2
          , primitive "__BOOT.realAdd" 0 2
          , primitive "__BOOT.ifRealLt" 1 4
          ]
  where
    mkTable l = M.fromList (mconcat l)
    primitive :: PrimitiveClosureHead -> Int -> Int -> [(Var, Value)]
    primitive h pn n =
      let
        clz = PrimitiveClosure h n NilPCS
        pclz = if pn > 0 then (PClosureV emptyEnv $ PrimitivePolyClz $ PolyPrimitiveClosure clz pn)
               else ClosureV emptyEnv $ PrimitiveClz clz
      in [(U.s2n h, pclz)]

isPrimitive :: Var -> Bool
isPrimitive x = M.member x primitives
