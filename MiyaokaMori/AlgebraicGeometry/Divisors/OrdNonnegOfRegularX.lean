import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrdNonnegOfRegular

/-! # Nonnegative order of a regular section

A section regular at `z` has nonnegative order of vanishing there: `0 ≤ ord_z a`. This is the
remark "its coefficients are regular at `z`" in the proof of Lemma 3.1 of
the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A nonzero section `a` over an open `U ∋ z` has nonnegative order of vanishing at `z`. -/
theorem ord_nonneg_of_regular {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    {U : X.Opens} [Nonempty U] {z : X} (hzU : z ∈ U) {a : Γ(X, U)} (ha : a ≠ 0) :
    0 ≤ X.ord (X.germToFunctionField U a) z := by
  exact (bridge_ord_nonneg hzU ha).2.2

end
