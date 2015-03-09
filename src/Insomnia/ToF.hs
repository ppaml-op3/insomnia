-- | Encoding of the Insomnia module calculus in System FΩ ala "F-ing
-- Modules".
--
-- We proceed in two steps: we translate module types into "semantic
-- signatures" which we then embed in FΩ.  Modules turn out to be
-- terms of the embedded types corresponding to their signatures.  The
-- key "trick" is that generativity is modeled by packing existential
-- types, and dependency (of later module components on prior ones) is
-- modeled by hoisting the scope of the existentials to enclose the
-- definition and the subsequent dependencies.
--
-- In this encoding, models end up encoding as something like "Dist
-- (∃α. τ)" where Dist is the probability distribution monad and τ is
-- the encoding of the underlying structure.  (One could also imagine
-- "∃α. Dist τ" which would correspond to all samples from a
-- distribution sharing the identity of their abstract types.  That is
-- not what we do in Insomnia, however.)
module Insomnia.ToF (Insomnia.ToF.Env.runToFM
                    , Insomnia.ToF.Module.moduleExpr
                    , Insomnia.ToF.ModuleType.moduleType
                    ) where


import Insomnia.ToF.Env
import Insomnia.ToF.ModuleType
import Insomnia.ToF.Module
