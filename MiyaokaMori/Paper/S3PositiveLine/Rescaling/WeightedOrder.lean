import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrderFinite

/-! # The weighted order

The weighted order `β_z = min_{i,q} ord_z(a_{α,i,q})/q ∈ ℚ` of a tuple of rational functions (with the
convention `ord_z 0 = +∞`); see §3 of the paper (equation (3.3)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The weighted order `β_z ∈ ℚ`: `weightedOrderTop` (the specialization of `MiyaokaMori.WeightedJets.weightedOrder`
to the jet weights and the order function `ordTop · z`) is finite on a nonzero tuple; this extracts its rational
value. The body is a term without embedded proofs; `hne` enters only through `weightedOrder_finite`. -/
def weightedOrderQ {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    {n κ : ℕ} (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0) (z : Ct.toScheme) : ℚ :=
  (weightedOrderTop a z).untop (weightedOrder_finite a hne z)

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} {n κ : ℕ}

theorem coe_weightedOrder (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0) (z : Ct.toScheme) :
    ((weightedOrderQ a hne z : ℚ) : WithTop ℚ) = weightedOrderTop a z :=
  WithTop.coe_untop _ _

/-- The minimum is attained at some nonzero coordinate. Downstream proofs use this instead of unfolding the definition. -/
theorem weightedOrder_attained (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0) (z : Ct.toScheme) :
    ∃ p : Fin (n + 1) × Fin κ, a p.1 p.2 ≠ 0 ∧
      weightedOrderQ a hne z = (Ct.toScheme.ord (a p.1 p.2) z : ℚ) / ((p.2 : ℕ) + 1) := by
  obtain ⟨p, hp0, hp⟩ := weightedOrderTop_attained a hne z
  exact ⟨p, hp0, WithTop.coe_injective (by rw [coe_weightedOrder, hp])⟩

/-- The weighted order is at most the normalized order of every nonzero coordinate. -/
theorem weightedOrder_le (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0) (z : Ct.toScheme) (i : Fin (n + 1)) (q : Fin κ) (hiq : a i q ≠ 0) :
    weightedOrderQ a hne z ≤ (Ct.toScheme.ord (a i q) z : ℚ) / ((q : ℕ) + 1) := by
  have h := weightedOrderTop_le a z (i, q)
  rw [← coe_weightedOrder a hne z, normalizedOrdTop_of_ne_zero a z (i, q) hiq] at h
  exact WithTop.coe_le_coe.mp h

end
