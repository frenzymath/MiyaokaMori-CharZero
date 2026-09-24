import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Orders of rational functions related by a stalk unit

The canonical image of a stalk unit has order zero on a locally Noetherian integral scheme.
Consequently, two nonzero rational functions whose quotient is such an image have the same order
at that point. This uses the actual local-ring order and canonical stalk-to-function-field map.

These are the local order comparisons needed for independence of the frame in a line-section
divisor and for the change-of-section formula. See the Stacks Project, Divisors,
`definition-order-vanishing-meromorphic` and `lemma-divisor-meromorphic-well-defined`.
-/

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Divisors.StalkUnitOrder

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- The canonical function-field image of an actual stalk unit has order zero at the same point. -/
theorem ord_algebraMap_unit (x : Y) (b : (Y.presheaf.stalk x)ˣ) :
    Y.ord (algebraMap (Y.presheaf.stalk x) Y.functionField (b : Y.presheaf.stalk x)) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have : Ring.KrullDimLE 1 (Y.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    have hb : algebraMap (Y.presheaf.stalk x) Y.functionField (b : Y.presheaf.stalk x) ≠ 0 :=
      (b.isUnit.map (algebraMap (Y.presheaf.stalk x) Y.functionField)).ne_zero
    apply (Scheme.ord_eq_iff hx hb).2
    change Ring.ordFrac (Y.presheaf.stalk x)
      (algebraMap (Y.presheaf.stalk x) Y.functionField (b : Y.presheaf.stalk x)) = 1
    exact Ring.ordFrac_of_isUnit b.isUnit
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- Nonzero rational functions whose quotient is a stalk unit have the same order there. -/
theorem ord_eq_of_div_eq_algebraMap_unit (x : Y) {f g : Y.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) (b : (Y.presheaf.stalk x)ˣ)
    (hfg : f / g =
      algebraMap (Y.presheaf.stalk x) Y.functionField (b : Y.presheaf.stalk x)) :
    Y.ord f x = Y.ord g x := by
  have hratio : Y.ord (f / g) x = 0 := by
    rw [hfg]
    exact ord_algebraMap_unit x b
  calc
    Y.ord f x = Y.ord ((f / g) * g) x := by rw [div_mul_cancel₀ f hg]
    _ = Y.ord (f / g) x + Y.ord g x := Scheme.ord_mul (div_ne_zero hf hg) hg
    _ = Y.ord g x := by rw [hratio, zero_add]

end AlgebraicGeometry.Divisors.StalkUnitOrder
