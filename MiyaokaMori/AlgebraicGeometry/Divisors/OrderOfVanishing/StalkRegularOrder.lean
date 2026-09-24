import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Nonnegative orders of nonzero regular local functions

For an integral locally Noetherian scheme, a nonzero element of an actual stalk has
nonnegative order after its canonical map to the function field. This also applies to a
nonzero regular section on an open neighbourhood. No normality or DVR hypothesis is needed:
at codimension one the order of a regular element comes from a nonnegative module length.

This supplies the local positivity step for the effective zero divisor of a nonzero line
section in the proofs of Lemma 3.1 and Theorem 4.2 of the paper.
It does not construct that divisor
or prove the degree comparison. The nonzero hypotheses exclude the junk value of `Scheme.ord`
at zero; away from codimension one the scheme's divisor coefficient is zero by definition.

Sources: Stacks Project, Divisors, `definition-order-vanishing`; Mathlib's
`Ring.ordFrac_ge_one_of_ne_zero` for one-dimensional Noetherian local domains.
-/

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Divisors.StalkRegularOrder

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A nonzero regular local function has nonnegative order at the same point. -/
theorem ord_algebraMap_nonneg (x : X) {a : X.presheaf.stalk x} (ha : a ≠ 0) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  by_cases hx : Order.coheight x = 1
  · have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    have hmap : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 := by
      intro hz
      apply ha
      exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
        (hz.trans (map_zero _).symm)
    apply (Scheme.le_ord_iff hx hmap).2
    change 1 ≤ Ring.ordFrac (X.presheaf.stalk x)
      (algebraMap (X.presheaf.stalk x) X.functionField a)
    exact Ring.ordFrac_ge_one_of_ne_zero ha
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- A nonzero section regular on a neighbourhood has nonnegative order there. -/
theorem ord_germToFunctionField_nonneg {U : X.Opens} [Nonempty U]
    {a : Γ(X, U)} (ha : a ≠ 0) {x : X} (hx : x ∈ U) :
    0 ≤ X.ord (X.germToFunctionField U a) x := by
  rw [← X.algebraMap_germ_eq_germToFunctionField hx a]
  apply ord_algebraMap_nonneg x
  intro hz
  apply ha
  exact germ_injective_of_isIntegral X x hx (hz.trans (map_zero _).symm)

end AlgebraicGeometry.Divisors.StalkRegularOrder
