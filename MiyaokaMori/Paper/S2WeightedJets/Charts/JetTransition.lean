import MiyaokaMori.Paper.S2WeightedJets.Charts.JetSubstitutionCoefficient
import MiyaokaMori.Paper.S2WeightedJets.Charts.TransitionPolynomial
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedAffineJetGrading
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic

/-! # The jet transition formula

The transition formula `x_{α',q} = g_{αα'} x_{α,q} + P_{αα',q}(x_{α,1}, …, x_{α,q-1})`
(eq. (2.7) of the paper): substitute the coefficient series into a formal
coordinate change without constant term and compare the coefficients of `t^q`; only finitely
many terms contribute, and the inverse transition has the same form.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem origin_baseCoordinate {R : Type u} [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    MiyaokaMori.BasedAffineJet.baseCoordinate (jetOriginSection (R := R) n) i = 0 := by
  simp [MiyaokaMori.BasedAffineJet.baseCoordinate, jetOriginSection]

private theorem universalCoordinate_mem {R : Type u} [CommRing R] (n k : ℕ)
    (i : Fin (n + 1)) :
    MiyaokaMori.BasedAffineJet.universalCoordinate (jetOriginSection (R := R) n) k i ∈
      Ideal.map (Polynomial.C :
        MvPolynomial (Fin (n + 1) × Fin k) R →+*
          Polynomial (MvPolynomial (Fin (n + 1) × Fin k) R))
        (MvPolynomial.idealOfVars (Fin (n + 1) × Fin k) R) := by
  rw [Ideal.mem_map_C_iff]
  intro d
  classical
  simp only [MiyaokaMori.BasedAffineJet.universalCoordinate, Polynomial.coeff_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C]
  split_ifs with hd
  · subst d
    simp [origin_baseCoordinate]
  · rw [zero_add]
    apply Ideal.sum_mem
    intro q hq
    simp only [Polynomial.coeff_monomial]
    split_ifs
    · exact Ideal.subset_span (Set.mem_range_self _)
    · exact Ideal.zero_mem _

private theorem linearRemainder_mem_square {R : Type u} [CommRing R] {s : ℕ}
    (p : MvPolynomial (Fin s) R) (h0 : p.coeff 0 = 0) :
    p - ∑ i, MvPolynomial.C (p.coeff (Finsupp.single i 1)) * MvPolynomial.X i ∈
      MvPolynomial.idealOfVars (Fin s) R ^ 2 := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff]
  intro m hm
  by_contra hdegree
  have hle : m.degree ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hdeg | hdeg
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hdeg
    subst m
    rw [MvPolynomial.mem_support_iff] at hm
    rw [MvPolynomial.coeff_sub, h0, MvPolynomial.coeff_sum] at hm
    simp [MvPolynomial.coeff_X] at hm
  · have hmrange : m ∈ Set.range (fun i : Fin s ↦ Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact hdeg
    obtain ⟨i, rfl⟩ := hmrange
    rw [MvPolynomial.mem_support_iff] at hm
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum] at hm
    simp [MvPolynomial.coeff_X,
      (Finsupp.single_left_injective (M := ℕ) one_ne_zero).eq_iff] at hm

private theorem universalEvaluation_coeff_mem_square {R : Type u} [CommRing R] (n k : ℕ)
    (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R ^ 2) (d : ℕ) :
    (MiyaokaMori.BasedAffineJet.universalEvaluation (jetOriginSection (R := R) n) k p).coeff d ∈
      MvPolynomial.idealOfVars (Fin (n + 1) × Fin k) R ^ 2 := by
  let e := MiyaokaMori.BasedAffineJet.universalEvaluation (jetOriginSection (R := R) n) k
  let I := MvPolynomial.idealOfVars (Fin (n + 1)) R
  let J := MvPolynomial.idealOfVars (Fin (n + 1) × Fin k) R
  have hmap : Ideal.map e.toRingHom I ≤
      Ideal.map (Polynomial.C :
        MvPolynomial (Fin (n + 1) × Fin k) R →+*
          Polynomial (MvPolynomial (Fin (n + 1) × Fin k) R)) J := by
    rw [Ideal.map_le_iff_le_comap]
    rw [show I = Ideal.span (Set.range MvPolynomial.X) from rfl, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change e (MvPolynomial.X i) ∈ Ideal.map Polynomial.C J
    simpa [e, MiyaokaMori.BasedAffineJet.universalEvaluation] using
      universalCoordinate_mem (R := R) n k i
  have hpmap : e p ∈ Ideal.map e.toRingHom (I ^ 2) := Ideal.mem_map_of_mem e.toRingHom hp
  rw [Ideal.map_pow] at hpmap
  have heval : e p ∈
      (Ideal.map (Polynomial.C :
        MvPolynomial (Fin (n + 1) × Fin k) R →+*
          Polynomial (MvPolynomial (Fin (n + 1) × Fin k) R)) J) ^ 2 := by
    rw [pow_two] at hpmap ⊢
    exact Ideal.mul_mono hmap hmap hpmap
  rw [← Ideal.map_pow] at heval
  exact (Ideal.mem_map_C_iff.mp heval) d

private theorem variable_weight_lt_of_degree_ge_two {σ : Type*} (w : σ → ℕ)
    (hw : ∀ i, w i ≠ 0) (m : σ →₀ ℕ) (hm : 2 ≤ m.degree) {i : σ}
    (hi : i ∈ m.support) : w i < Finsupp.weight w m := by
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hrem : m - Finsupp.single i 1 ≠ 0 := by
    intro hzero
    have hm_single : m = Finsupp.single i 1 := by
      rw [← Finsupp.sub_add_single_one_cancel hmi, hzero, zero_add]
    rw [hm_single] at hm
    simp at hm
  let _ : Finsupp.NonTorsionWeight ℕ w := Finsupp.nonTorsionWeight_of (w := w) ℕ hw
  have hweight_ne : Finsupp.weight w (m - Finsupp.single i 1) ≠ 0 := by
    intro hzero
    exact hrem ((Finsupp.weight_eq_zero_iff_eq_zero w).mp hzero)
  have hsplit := Finsupp.weight_sub_single_add (w := w) hmi
  omega

private theorem universalCoordinate_coeff_succ {R : Type u} [CommRing R] (n k : ℕ)
    (i : Fin (n + 1)) (q : Fin k) :
    (MiyaokaMori.BasedAffineJet.universalCoordinate (jetOriginSection (R := R) n) k i).coeff
      (q.val + 1) = MvPolynomial.X (i, q) := by
  classical
  simp only [MiyaokaMori.BasedAffineJet.universalCoordinate, Polynomial.coeff_add,
    Polynomial.coeff_C_succ, zero_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Nat.add_right_cancel_iff, Fin.val_inj]
  simp

private theorem universalEvaluation_linear_coeff {R : Type u} [CommRing R] (n k : ℕ)
    (a : Fin (n + 1) → R) (q : Fin k) :
    (MiyaokaMori.BasedAffineJet.universalEvaluation (jetOriginSection (R := R) n) k
      (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j)).coeff (q.val + 1) =
        ∑ j, MvPolynomial.C (a j) * MvPolynomial.X (j, q) := by
  classical
  simp only [map_sum, map_mul, MiyaokaMori.BasedAffineJet.universalEvaluation,
    MvPolynomial.aeval_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [universalCoordinate_coeff_succ]

theorem jet_transition_formula {R : Type u} [CommRing R] (n k : ℕ)
    (Φ : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] MvPowerSeries (Fin (n + 1)) R)
    (hΦ : ∀ i, MvPowerSeries.constantCoeff (Φ (MvPowerSeries.X i)) = 0)
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hg : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (Φ (MvPowerSeries.X i)) = g i j)
    (q : Fin k) :
    ∃ P : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin k) R,
      (∀ i, IsJetTransitionPolynomial n k ((q : ℕ) + 1) (P i)) ∧
      ∀ i, jetSubstitutionCoeff n k Φ i ((q : ℕ) + 1) =
        (∑ j, MvPolynomial.C (g i j) * MvPolynomial.X (j, q)) + P i := by
  classical
  let b : Fin (n + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ ↦ q.val + 1)
  let p (i : Fin (n + 1)) := MvPowerSeries.trunc' R b (Φ (MvPowerSeries.X i))
  let r (i : Fin (n + 1)) :=
    p i - ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j
  let P (i : Fin (n + 1)) :=
    (MiyaokaMori.BasedAffineJet.universalEvaluation (jetOriginSection (R := R) n) k
      (r i)).coeff (q.val + 1)
  have hp0 (i : Fin (n + 1)) : (p i).coeff 0 = 0 := by
    dsimp only [p]
    rw [MvPowerSeries.coeff_trunc', if_pos (by intro; simp)]
    exact hΦ i
  have hp1 (i j : Fin (n + 1)) : (p i).coeff (Finsupp.single j 1) = g i j := by
    dsimp only [p]
    rw [MvPowerSeries.coeff_trunc', if_pos]
    · exact hg i j
    · intro l
      classical
      by_cases h : l = j <;> simp [b, h]
  have hr (i : Fin (n + 1)) :
      r i ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R ^ 2 := by
    simpa only [r, hp1] using linearRemainder_mem_square (p i) (hp0 i)
  refine ⟨P, ?_, ?_⟩
  · intro i
    have hweighted : MvPolynomial.IsWeightedHomogeneous
        (fun iq : Fin (n + 1) × Fin k ↦ iq.2.val + 1) (P i) (q.val + 1) := by
      exact MiyaokaMori.BasedAffineJetGrading.universalEvaluation_coeff_isWeightedHomogeneous
        (jetOriginSection (R := R) n) k (r i) (q.val + 1)
    have hdegree : ∀ m ∈ (P i).support, 2 ≤ m.sum (fun _ e ↦ e) := by
      intro m hm
      have hmem := universalEvaluation_coeff_mem_square n k (r i) (hr i) (q.val + 1)
      rw [MvPolynomial.mem_pow_idealOfVars_iff] at hmem
      exact hmem m hm
    refine ⟨hweighted, hdegree, ?_⟩
    intro m hm iq hiq
    rw [← hweighted (MvPolynomial.mem_support_iff.mp hm)]
    exact variable_weight_lt_of_degree_ge_two
      (fun jq : Fin (n + 1) × Fin k ↦ jq.2.val + 1) (by intro; omega) m
      (hdegree m hm) hiq
  · intro i
    change (MiyaokaMori.BasedAffineJet.universalEvaluation (jetOriginSection (R := R) n) k
      (p i)).coeff (q.val + 1) =
        (∑ j, MvPolynomial.C (g i j) * MvPolynomial.X (j, q)) + P i
    have hdecomp : p i = (∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) + r i := by
      simp [r]
    rw [hdecomp, map_add, Polynomial.coeff_add, universalEvaluation_linear_coeff]

end
