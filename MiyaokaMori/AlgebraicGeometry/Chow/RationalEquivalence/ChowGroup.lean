import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs

/-! # The Chow group of a variety

The `i`-dimensional Chow group `A_i(X) = Z_i(X) / (rational equivalence)` of a variety (Fulton, Intersection
Theory, §1.3). There is **one** Chow group: the Chow group of a variety `X` is the Chow group of its
underlying scheme, `AlgebraicGeometry.ChowGroup X.toScheme i`
(`Z_i(X) ⧸ (ratEquivZero X i).addSubgroupOf (cycleSubgroup X i)`, rational equivalence in the sense of
Stacks 02RW). Fulton's description of the generators (pushforwards of principal divisors on
`(i+1)`-dimensional closed subvarieties `W`) is the theorem
`ClosedSubvariety.properPushforward_principalDivisor_mem_ratEquivZero` (`RationalEquivalence.lean`).
The `AddCommGroup (ChowGroup X i)` instance is the scheme-level one through the `abbrev` (no second
instance is registered). The imports of this module are kept so that its import closure is unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `i`-dimensional Chow group of a variety `X`: the Chow group of the underlying scheme
(`AlgebraicGeometry.ChowGroup`, rational equivalence in the sense of Stacks 02RW). -/
abbrev ChowGroup {k : Type u} [Field k] (X : Variety k) (i : ℕ) : Type u :=
  AlgebraicGeometry.ChowGroup X.toScheme i

end
