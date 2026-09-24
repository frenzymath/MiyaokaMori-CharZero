import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.Paper.S2WeightedJets.Ygg.SumLtOfAllLt

/-! # Monomials of large weight are divisible by a weight-power

A monomial in `s` weighted variables of weight greater than `m = s · w_k` is divisible by
some `x_i^{w_k / q_i}`: otherwise each of the `s` variables would contribute less than `w_k`
to the weight, and the total weight would be less than `m`
(proof of Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem exists_pow_dvd_of_weight_gt {s k : ℕ} (w : Fin s → ℕ)
    (hw : ∀ i, w i ∈ Finset.Icc 1 k) (e : Fin s →₀ ℕ)
    (h : s * jetWeight k < Finsupp.weight w e) :
    ∃ i, jetWeight k / w i ≤ e i := by
  classical
  have hweight : Finsupp.weight w e = ∑ i : Fin s, w i * e i := by
    rw [Finsupp.weight_eq_sum]
    simp [smul_eq_mul, Nat.mul_comm]
  have hsum : s * jetWeight k < ∑ i : Fin s, w i * e i := by
    simpa [hweight] using h
  obtain ⟨i, hi⟩ := exists_ge_of_card_mul_lt_sum (fun i => w i * e i) (jetWeight k) hsum
  have hdvd : w i ∣ jetWeight k := by
    simpa [jetWeight] using
      (Finset.dvd_lcm (s := Finset.Icc 1 k) (f := id) (b := w i) (hw i))
  have hwpos : 0 < w i := (Finset.mem_Icc.mp (hw i)).1
  have hmul : (jetWeight k / w i) * w i ≤ w i * e i := by
    rw [Nat.div_mul_cancel hdvd]
    exact hi
  exact ⟨i, Nat.le_of_mul_le_mul_left (a := jetWeight k / w i) (b := e i) (c := w i)
    (by simpa [Nat.mul_comm] using hmul) hwpos⟩

end
