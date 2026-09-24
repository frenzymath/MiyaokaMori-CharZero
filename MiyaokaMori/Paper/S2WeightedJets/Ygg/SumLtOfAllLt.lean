import MiyaokaMori.Prelude

/-! # A pigeonhole bound

If the sum of `s` natural numbers exceeds `s · W`, then one of them is at least `W`
(the counting step in the proof of Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem exists_ge_of_card_mul_lt_sum {s : ℕ} (f : Fin s → ℕ) (W : ℕ)
    (h : s * W < ∑ i, f i) : ∃ i, W ≤ f i := by
  classical
  by_contra hn
  push_neg at hn
  by_cases hW : W = 0
  · subst W
    by_cases hs : 0 < s
    · exact (Nat.not_lt_zero _ (hn ⟨0, hs⟩))
    · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
      subst s
      simpa using h
  · have hWpos : 0 < W := Nat.pos_of_ne_zero hW
    have hle : ∀ i : Fin s, f i + 1 ≤ W := by
      intro i
      have hi := hn i
      omega
    have hsum : (∑ i, f i) + s ≤ s * W := by
      calc
        (∑ i, f i) + s = ∑ i : Fin s, (f i + 1) := by simp [Finset.sum_add_distrib]
        _ ≤ ∑ _i : Fin s, W := Finset.sum_le_sum (fun i hi => hle i)
        _ = s * W := by simp [Nat.mul_comm]
    omega

end
