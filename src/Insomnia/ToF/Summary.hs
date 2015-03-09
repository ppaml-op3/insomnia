-- | Intermediate results collected in the course of the Insomnia→FΩ translation.
module Insomnia.ToF.Summary where

import Data.Monoid (Endo)

import Unbound.Generics.LocallyNameless (Embed)

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

-- | An unpacked form of an 'FOmega.SemanticSig.AbstractSig'.
--   ∃ αs:κs . fs:Σs
--
-- We make use of the fact that a 'SigSummary' is a 'Monoid'.
--
type ExposedAbstractSig v = ([(F.TyVar, Embed F.Kind)], [(v, F.SemanticSig)])

-- | The result of translating a signature, in unpacked form.
type SigSummary = ExposedAbstractSig F.Field

-- | A module summary is a triple (sigSummary, fieldAssigns, termCtx)
-- the signature summary gives the type of the module.  The field
-- assignments provide a list of terms that will be used to populate
-- the module record.  The termCtx sets up the environment for the
-- field assigns (for example by unpacking existentials, etc).  The
-- abstract type variables from the sig summary are assumed to scope
-- over the field assigns and will be packed when the module record is
-- constructed.
--
-- example:
-- @@@
--   (([α:⋆], "M" : ..., "x" : [:α])
--   , ["M" = m, "x" = x]
--   , unpack α,m = M in let x = {val = m.z.val} in •)
-- @@@
-- is the mod summary for something like:
-- @@@
--  module { module M : { type t; z : t } = ... ; val x = M.z }
-- @@@
-- and will be packaged up as the term
-- @@@
--  unpack α,m = M in
--  let x = {val = m.z.val} in
--  pack α, {"M" = m, "x" = x}
--    as ∃α:⋆.{"M" : ..., "x" : [:α]}
-- @@@
--
-- (We partition the term into a field assignment and a termCtx in
-- order to avoid some gratuitous intermediate unpacking and repacking
-- of existential types.  Ie, we're doing some of the commuting
-- conversions for unpack-let, unpack-unpack, and let-let at
-- construction-time.)
--
-- Note that this type is also a Monoid. So we can build up ModSummary values incrementally
type ModSummary = (SigSummary, [(F.Field, F.Term)], Endo F.Term)
