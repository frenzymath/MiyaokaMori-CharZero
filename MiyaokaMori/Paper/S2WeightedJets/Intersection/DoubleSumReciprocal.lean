import MiyaokaMori.Prelude

/-! # A double sum of reciprocals

Rearranging a double sum (pure combinatorics): `Σ_{i∈s} Σ_{q=1}^{k} (e_i : ℚ)/q = (Σ_{i∈s} e_i) · h_k`, where
`h_k = Σ_{q=1}^{k} 1/q` (the final step of Proposition 2.4 of the paper, eq. (2.9)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem sum_sum_div_eq_sum_mul_harmonic {ι : Type*} (s : Finset ι) (e : ι → ℤ) (kk : ℕ) :
    ∑ i ∈ s, ∑ q ∈ Finset.Icc 1 kk, (e i : ℚ) / (q : ℚ)
      = (∑ i ∈ s, (e i : ℚ)) * ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
  let t : Finset ℕ := Finset.Icc 1 kk
  calc
    ∑ i ∈ s, ∑ q ∈ Finset.Icc 1 kk, (e i : ℚ) / (q : ℚ)
        = ∑ i ∈ s, ∑ q ∈ t, (e i : ℚ) * ((1 : ℚ) / (q : ℚ)) := by
            simp [t, div_eq_mul_inv]
    _ = ∑ i ∈ s, (e i : ℚ) * ∑ q ∈ t, (1 : ℚ) / (q : ℚ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
    _ = (∑ i ∈ s, (e i : ℚ)) * ∑ q ∈ t, (1 : ℚ) / (q : ℚ) := by
            rw [Finset.sum_mul]
    _ = (∑ i ∈ s, (e i : ℚ)) * ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
            rfl

end
