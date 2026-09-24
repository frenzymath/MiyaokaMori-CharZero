import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The additive valuation of a curve stalk

For a codimension-one point of a locally Noetherian integral scheme whose stalk is a DVR,
this module puts the canonical order of vanishing on the scheme's own function field into
`AddValuation` form. Zero has order `⊤`. On nonzero functions the value is Mathlib's
`Scheme.ord`, and nonnegative value is equivalent to coming from the actual stalk.

This is the local algebra bridge for the order computations in the proof of Lemma 3.1 of the paper. It does not assert that
an arbitrary `SmoothProjectiveCurve` has these geometric properties; deriving integrality,
local Noetherianity, codimension one at closed points, and the DVR stalks is a separate task.

The construction uses Mathlib's `Scheme.ordHom` and `Ring.ordFrac`. In a DVR the latter
agrees with the inverse of the maximal-ideal adic valuation, normalized to give a local
parameter order one. No new function field or arbitrary valuation is introduced.
-/

noncomputable section

open AlgebraicGeometry Order

namespace AlgebraicGeometry.Divisors.CurveStalkValuation

universe u

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
variable (x : X) (hx : coheight x = 1)

include x hx

/-- The stalk order, with infinity at zero and the usual integer order elsewhere. -/
def order (f : X.functionField) : WithTop ℤ :=
  by
    classical
    exact if hf : f = 0 then ⊤ else
      ((WithZero.unzero ((map_ne_zero (X.ordHom x hx)).mpr hf)).toAdd : ℤ)

/-- The zero rational function has infinite order. -/
@[simp] theorem order_zero : order X x hx 0 = ⊤ := by
  simp [order]

/-- Away from zero, the order is exactly Mathlib's geometric order of vanishing. -/
theorem order_of_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    order X x hx f = (X.ord f x : WithTop ℤ) := by
  simp only [order, dif_neg hf, Scheme.ord_eq_unzero_ordHom hx hf]

/-- The constant function one has order zero. -/
@[simp] theorem order_one : order X x hx 1 = 0 := by
  rw [order_of_ne_zero X x hx one_ne_zero,
    Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  simp [WithZero.unzeroD]

/-- Multiplication adds orders, including products with zero. -/
theorem order_mul (f g : X.functionField) :
    order X x hx (f * g) = order X x hx f + order X x hx g := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  rw [order_of_ne_zero X x hx (mul_ne_zero hf hg), order_of_ne_zero X x hx hf,
    order_of_ne_zero X x hx hg, Scheme.ord_mul hf hg, WithTop.coe_add]

variable [hDVR : IsDiscreteValuationRing (X.presheaf.stalk x)]

include hDVR

/-- The DVR order satisfies the valuation inequality, including cancellation to zero. -/
theorem order_add (f g : X.functionField) :
    min (order X x hx f) (order X x hx g) ≤ order X x hx (f + g) := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases hfg : f + g = 0
  · simp [hfg]
  rw [order_of_ne_zero X x hx hf, order_of_ne_zero X x hx hg,
    order_of_ne_zero X x hx hfg, ← WithTop.coe_min, WithTop.coe_le_coe]
  exact Scheme.ord_add hfg

/-- The normalized additive valuation on the same scheme function field. -/
def valuation : AddValuation X.functionField (WithTop ℤ) :=
  AddValuation.of (order X x hx) (order_zero X x hx) (order_one X x hx)
    (order_add X x hx) (order_mul X x hx)

/-- Unbundling the valuation gives the canonical stalk order. -/
theorem valuation_apply (f : X.functionField) : valuation X x hx f = order X x hx f := rfl

/-- For a nonzero rational function the valuation is the ordinary geometric order. -/
theorem valuation_of_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    valuation X x hx f = (X.ord f x : WithTop ℤ) :=
  order_of_ne_zero X x hx hf

/-- A regular stalk element has nonnegative order after passing to the function field. -/
theorem valuation_algebraMap_nonneg (a : X.presheaf.stalk x) :
    0 ≤ valuation X x hx (algebraMap (X.presheaf.stalk x) X.functionField a) := by
  by_cases ha : a = 0
  · simp [ha]
  have ha' : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 := by
    intro h
    apply ha
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by simpa using h)
  rw [valuation_of_ne_zero X x hx ha']
  change ((0 : ℤ) : WithTop ℤ) ≤ _
  apply WithTop.coe_le_coe.mpr
  apply (Scheme.le_ord_iff hx ha').mpr
  simpa only [ofAdd_zero, WithZero.coe_one, Scheme.ordHom] using
    (Ring.ordFrac_ge_one_of_ne_zero (R := X.presheaf.stalk x)
      (K := X.functionField) ha)

/-- Nonnegative valuation means actual membership in the image of the stalk. -/
theorem valuation_nonneg_iff (f : X.functionField) :
    0 ≤ valuation X x hx f ↔
      ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = f := by
  constructor
  · intro h
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    rw [valuation_of_ne_zero X x hx hf] at h
    have hord : 0 ≤ X.ord f x := WithTop.coe_le_coe.mp h
    have hfrac : 1 ≤ Ring.ordFrac (X.presheaf.stalk x) f := by
      simpa only [ofAdd_zero, WithZero.coe_one, Scheme.ordHom] using
        (Scheme.le_ord_iff hx hf).mp hord
    rw [Ring.ordFrac_eq_valuation_inv] at hfrac
    exact IsDiscreteValuationRing.exists_lift_of_le_one (one_le_inv_iff₀.mp hfrac).2
  · rintro ⟨a, rfl⟩
    exact valuation_algebraMap_nonneg X x hx a

/-- A section regular on an open neighbourhood has nonnegative valuation. -/
theorem valuation_germToFunctionField_nonneg {U : X.Opens} [Nonempty U]
    (hxU : x ∈ U) (s : Γ(X, U)) :
    0 ≤ valuation X x hx (X.germToFunctionField U s) := by
  rw [← X.algebraMap_germ_eq_germToFunctionField hxU s]
  exact valuation_algebraMap_nonneg X x hx (X.presheaf.germ U x hxU s)

/-- A unit of the actual local ring has order zero. -/
theorem valuation_algebraMap_of_isUnit {a : X.presheaf.stalk x} (ha : IsUnit a) :
    valuation X x hx (algebraMap (X.presheaf.stalk x) X.functionField a) = 0 := by
  have ha' : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
    (ha.map (algebraMap (X.presheaf.stalk x) X.functionField)).ne_zero
  rw [valuation_of_ne_zero X x hx ha']
  have hord : X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
    apply (Scheme.ord_eq_iff hx ha').mpr
    simpa only [Scheme.ordHom, ofAdd_zero, WithZero.coe_one] using
      (Ring.ordFrac_of_isUnit (K := X.functionField) ha)
  simp [hord]

/-- A local parameter has order one, fixing the normalization of the valuation. -/
theorem valuation_algebraMap_irreducible {a : X.presheaf.stalk x} (ha : Irreducible a) :
    valuation X x hx (algebraMap (X.presheaf.stalk x) X.functionField a) = 1 := by
  have ha' : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 := by
    intro h
    apply ha.ne_zero
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by simpa using h)
  rw [valuation_of_ne_zero X x hx ha']
  have hord : X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 1 := by
    apply (Scheme.ord_eq_iff hx ha').mpr
    simpa only [Scheme.ordHom, WithZero.exp_eq_coe_ofAdd] using
      (Ring.ordFrac_irreducible (K := X.functionField) ha)
  simp [hord]

end AlgebraicGeometry.Divisors.CurveStalkValuation
