import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.StalkRegularOrder

/-! # Nonnegative order of a regular section (bridge form)

A regular section has nonnegative order of vanishing: `ord 1 = 0`, `a • 1` is the image of `a` in
the function field, and `0 ≤ ord_z a`. This packages the three facts used to bound the weighted
order (3.3) in the proof of Lemma 3.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

/-- For a nonzero section `a` over an open `U ∋ z`: `ord_z 1 = 0`, `a • 1` is the germ of `a` in
the function field, and its order at `z` is nonnegative. -/
theorem bridge_ord_nonneg {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    {U : X.Opens} [Nonempty U] {z : X} (hzU : z ∈ U) {a : Γ(X, U)} (ha : a ≠ 0) :
    X.ord (1 : X.functionField) z = 0 ∧
    (a • (1 : X.functionField)) = X.germToFunctionField U a ∧
    0 ≤ X.ord (X.germToFunctionField U a) z := by
  have h1 := X.ord_of_isUnit (U := U) (f := (1 : Γ(X, U))) isUnit_one hzU
  refine ⟨by simpa using h1, ?_,
    AlgebraicGeometry.Divisors.StalkRegularOrder.ord_germToFunctionField_nonneg ha hzU⟩
  simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end
