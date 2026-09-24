import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Choosing the harmonic jet order for polynomial realization

The order choice in the paper (equation (4.2) of Theorem 4.2) requires
`d * harmonic k > 2 * (n + 1) * δ * a`. For positive `d`, Mathlib's logarithmic
lower bound on the actual rational harmonic sum supplies such an order beyond
any prescribed natural cutoff. No positivity of `a` or nonzero condition on
`n` or `δ` is needed for this choice.

The resulting strict inequality specializes the `horder` input of
`MiyaokaMori.Jet.equation_degreeFloor_lt_order` to `h = harmonic k`. The positive
line-bundle slope and coefficient bounds remain the geometric caller's tasks;
this theorem does not construct positive jets or prove polynomial realization.
-/

namespace MiyaokaMori.Jet

/-- Choose a positive jet order beyond any cutoff satisfying the paper's strict harmonic
inequality. The harmonic sum is Mathlib's sum of the reciprocals from `1` through `k`. -/
theorem exists_realization_order (d a : ℚ) (n δ N : ℕ) (hd : 0 < d) :
    ∃ k : ℕ, max 1 N ≤ k ∧
      2 * ((n : ℚ) + 1) * (δ : ℚ) * a < d * harmonic k := by
  let B : ℚ := 2 * ((n : ℚ) + 1) * (δ : ℚ) * a
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp ((B / d : ℚ) : ℝ))
  let k := max (max 1 N) m
  refine ⟨k, le_max_left _ _, ?_⟩
  have hmk : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
  have hks : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_lt.mpr (Nat.lt_succ_self k)
  have hlog : ((B / d : ℚ) : ℝ) < Real.log ((k + 1 : ℕ) : ℝ) :=
    (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr (Nat.succ_pos k))).mpr
      ((hm.trans_le hmk).trans hks)
  have hbound : B / d < harmonic k :=
    Rat.cast_lt.mp (hlog.trans_le (log_add_one_le_harmonic k))
  change B < d * harmonic k
  simpa only [mul_comm] using (div_lt_iff₀ hd).mp hbound

end MiyaokaMori.Jet
