import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # The order of vanishing is zero exactly for units

In a one-dimensional Noetherian local domain `R` (Krull dimension `≤ 1`), the order of vanishing
`ord(c) = length(R/(c))` of a nonzero element `c` is `0` iff `c` is a unit:
`R/(c)` has length `0 ⟺ R/(c) = 0 ⟺ (c) = R ⟺ c` is a unit.
Scheme version: at a point `x` of codimension `1` of an integral locally Noetherian scheme `X`, a nonzero
nonunit stalk element `c` has `ord_x(c) ≠ 0`. (Auxiliary to the support of the fibre divisor.)

References: Stacks 02MD (definition of the order of vanishing as `length(R/(c))`); Hartshorne II.6 (the
coefficients of a Weil divisor are orders of vanishing).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For a nonzero element `c` of a one-dimensional Noetherian domain `R`: `ordFrac(c) = 1` (i.e. `ord(c) = 0`) ⇒
`c` is a unit. `length(R/(c)) = 0 ⇒ R/(c)` is trivial `⇒ (c) = ⊤ ⇒ c` is a unit. -/
theorem Ring.isUnit_of_ordFrac_eq_one {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x : R} (hx : x ≠ 0) (h : Ring.ordFrac R (algebraMap R K x) = 1) : IsUnit x := by
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_ord hnz] at h
  have hord : Ring.ord R x = 0 := by
    generalize Ring.ord R x = n at h
    cases n with
    | top => simp at h
    | coe n =>
      simp only [ENat.recTopCoe_natCast] at h
      rw [← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one] at h
      exact_mod_cast h
  have hlen : Module.length R (R ⧸ Ideal.span {x}) = 0 := hord
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hlen
  exact hlen

/-- At a point `x` of codimension `1` of an integral locally Noetherian scheme `X`, a nonzero nonunit stalk
element `c` has nonzero order of vanishing. -/
theorem AlgebraicGeometry.Scheme.ord_algebraMap_ne_zero_of_not_isUnit
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1) {c : X.presheaf.stalk x} (hc0 : c ≠ 0) (hc : ¬ IsUnit c) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField c) x ≠ 0 := by
  intro h
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hx.le
  have hne : algebraMap (X.presheaf.stalk x) X.functionField c ≠ 0 := by
    intro h0
    apply hc0
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by simpa using h0)
  rw [AlgebraicGeometry.Scheme.ord_eq_iff hx hne] at h
  apply hc
  apply Ring.isUnit_of_ordFrac_eq_one (K := X.functionField) hc0
  simpa [AlgebraicGeometry.Scheme.ordHom] using h

end
