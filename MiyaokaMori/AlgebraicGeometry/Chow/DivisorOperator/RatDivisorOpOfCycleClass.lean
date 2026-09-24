import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitTautologicalClass

/-! # A ℚ-divisor operator from a family of dimension-lowering Chow operators

A dimension-indexed family of dimension-lowering operators `H_d : CH_d(X)_ℚ → CH_{d−1}(X)_ℚ` on the
Chow groups (such as `splitTautologicalClass`) is packaged as a single ℚ-divisor operator
`RatDivisorOp X` (whose `d`-th component is `H_{d+1}`). Notation for the class `H^sp` of (2.10) of the paper. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The ℚ-divisor operator whose `d`-th component is `H (d + 1)`. -/
noncomputable def ratDivisorOpOfCycleClass {X : AlgebraicGeometry.Scheme.{u}}
    (H : ∀ d : ℕ, AlgebraicGeometry.ChowGroupRat X d →ₗ[ℚ] AlgebraicGeometry.ChowGroupRat X (d - 1)) :
    AlgebraicGeometry.RatDivisorOp X :=
  fun d => H (d + 1)   -- `(d + 1) - 1` and `d` are definitionally equal

end
