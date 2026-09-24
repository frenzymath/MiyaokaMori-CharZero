import MiyaokaMori.Prelude

/-! # Coefficients above the degree vanish

If `degree f < κ`, then every coefficient of `f` with index `≥ κ` is zero. This lifts
`coeff_eq_zero_of_degree_lt` from a single index to the whole range of indices; the only
work is the cast `κ ≤ q ⇒ (κ : WithBot ℕ) ≤ q` and transitivity.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem coeff_eq_zero_of_ge_of_degree_lt {R : Type*} [CommRing R] {f : Polynomial R}
    {κ q : ℕ} (hdeg : f.degree < (κ : WithBot ℕ)) (hq : κ ≤ q) : f.coeff q = 0 := by
  exact (Polynomial.degree_lt_iff_coeff_zero f κ).1 hdeg q hq

end
