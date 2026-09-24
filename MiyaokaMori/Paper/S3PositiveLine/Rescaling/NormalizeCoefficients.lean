import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrder
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.FunctionFieldOrderPowers

/-! # Normalizing the coefficients

After replacing the weight-`q` coordinates by `γ^{-q}a_{α,i,q}`, they are regular at every point and at least one
of them is a unit (by the definition of the minimal weighted order); §3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The order of a normalized nonzero coordinate: `ord(γ^{-(q+1)} a_{i,q}) = ord a_{i,q} - (q+1)·ord γ`
(`Scheme.ord_mul` and `FunctionFieldOrderPowers.ord_zpow`). -/
theorem ord_normalized_coefficient {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (γ f : Ct.toScheme.functionField) (hγ0 : γ ≠ 0) (hf : f ≠ 0) (w : ℤ) (z : Ct.toScheme) :
    Ct.toScheme.ord (γ ^ (-w) * f) z = Ct.toScheme.ord f z - w * Ct.toScheme.ord γ z := by
  rw [AlgebraicGeometry.Scheme.ord_mul (zpow_ne_zero _ hγ0) hf,
    AlgebraicGeometry.Divisors.FunctionFieldOrderPowers.ord_zpow hγ0]
  ring

theorem normalized_coefficients_regular_and_unit {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0)
    (V : Ct.toScheme.Opens) (γ : Ct.toScheme.functionField) (hγ0 : γ ≠ 0)
    (hγ : ∀ z ∈ V, (Ct.toScheme.ord γ z : ℚ) = weightedOrderQ a hne z)
    (z : Ct.toScheme) (hz : z ∈ V) :
    (∀ i (q : Fin κ), 0 ≤ Ct.toScheme.ord (γ ^ (-((q : ℕ) + 1 : ℤ)) * a i q) z) ∧
    (∃ (i : Fin (n + 1)) (q : Fin κ), γ ^ (-((q : ℕ) + 1 : ℤ)) * a i q ≠ 0 ∧
      Ct.toScheme.ord (γ ^ (-((q : ℕ) + 1 : ℤ)) * a i q) z = 0) := by
  have hβ := hγ z hz
  constructor
  · intro i q
    by_cases hiq : a i q = 0
    · simp [hiq, AlgebraicGeometry.Scheme.ord_zero]
    · rw [ord_normalized_coefficient γ _ hγ0 hiq]
      have hle := weightedOrder_le a hne z i q hiq
      rw [← hβ, le_div_iff₀ (by positivity)] at hle
      have : ((((q : ℕ) + 1 : ℤ) * Ct.toScheme.ord γ z : ℤ) : ℚ) ≤
          (Ct.toScheme.ord (a i q) z : ℚ) := by
        push_cast; linarith
      exact sub_nonneg.mpr (by exact_mod_cast this)
  · obtain ⟨p, hp0, hp⟩ := weightedOrder_attained a hne z
    refine ⟨p.1, p.2, mul_ne_zero (zpow_ne_zero _ hγ0) hp0, ?_⟩
    rw [ord_normalized_coefficient γ _ hγ0 hp0]
    rw [← hβ, eq_div_iff (by positivity)] at hp
    have : ((((p.2 : ℕ) + 1 : ℤ) * Ct.toScheme.ord γ z : ℤ) : ℚ) =
        (Ct.toScheme.ord (a p.1 p.2) z : ℚ) := by
      push_cast; linarith
    exact sub_eq_zero.mpr (by exact_mod_cast this.symm)

end
