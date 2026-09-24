import MiyaokaMori.Prelude

/-! # Mixed differences of polynomials of bounded total degree

Pure `MvPolynomial` algebra: the `(d+1)`-fold mixed difference at the origin of a polynomial in `d+1`
variables of total degree `≤ d` vanishes:
`∑_{S ⊆ Fin (d+1)} (-1)^{d+1-|S|} P(1_S) = 0`.

References: the last step of the proof of Stacks 0BEU (comparing leading coefficients); the remark after the
definition in Stacks 0BEP (the coefficient of `n_1⋯n_d` in a numerical polynomial is a `d`-fold mixed
difference).

Use: in Stacks 0BEU, the difference of `(L_0⋯L_d·X)` and `(L_1|_D⋯L_d|_D·D)` is written as the `(d+1)`-fold
mixed difference of `χ` of the `d+1` line bundles `ι^*L_0,…,ι^*L_d` on `D`; by 0BEM,
`n ↦ χ(D, ⊗(ι^*L_i)^{n_i})` is a numerical polynomial of total degree `≤ dim D = d`, so this lemma makes it
vanish.

Proof: `mixed_difference_eq_coeff` (below) turns the mixed difference into the coefficient of the monomial
`n_0⋯n_d`, whose degree `d+1` exceeds `totalDegree P`, so it is `0`
(`MvPolynomial.coeff_eq_zero_of_totalDegree_lt`).

The first three lemmas duplicate private lemmas of the module `Stacks0bepLemmas`, which cannot be referenced
from here. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace MvPolynomial

/-- Products of indicator functions raised to powers: `∏_{i} (1_{i∈t})^{u i} = ∏_{i ∉ t} 0^{u i}` (with the
convention `0^0 = 1`). -/
theorem prod_indicator_pow_sdiff {d : ℕ} (u : Fin d →₀ ℕ) (t : Finset (Fin d)) :
    (∏ i : Fin d, (if i ∈ t then (1 : ℚ) else 0) ^ u i)
      = ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i := by
  classical
  rw [← Finset.prod_sdiff (Finset.subset_univ t)]
  have h1 : (∏ i ∈ t, (if i ∈ t then (1 : ℚ) else 0) ^ u i) = 1 :=
    Finset.prod_eq_one fun i hi => by rw [if_pos hi, one_pow]
  have h2 : (∏ i ∈ Finset.univ \ t, (if i ∈ t then (1 : ℚ) else 0) ^ u i)
      = ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i :=
    Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.mem_sdiff.mp hi).2]
  rw [h1, h2, mul_one]

/-- The mixed difference on a monomial `X^u`:
`∑_{S ⊆ {1..d}} (-1)^{d-|S|} ∏_i (1_{i∈S})^{u i} = ∏_i (1 - 0^{u i})`. -/
theorem alternating_sum_indicator_prod_eq {d : ℕ} (u : Fin d →₀ ℕ) :
    (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        ∏ i : Fin d, (if i ∈ S then (1 : ℚ) else 0) ^ u i)
      = ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) := by
  classical
  have key := Finset.prod_add (fun _ : Fin d => (1 : ℚ)) (fun i => -((0 : ℚ) ^ u i)) Finset.univ
  rw [Finset.powerset_univ] at key
  have hl : (∏ i : Fin d, ((1 : ℚ) + -((0 : ℚ) ^ u i))) = ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) :=
    Finset.prod_congr rfl fun i _ => by ring
  have hr : ∀ t : Finset (Fin d),
      ((∏ _i ∈ t, (1 : ℚ)) * ∏ i ∈ Finset.univ \ t, -((0 : ℚ) ^ u i))
        = (-1 : ℚ) ^ (d - t.card) * ∏ i : Fin d, (if i ∈ t then (1 : ℚ) else 0) ^ u i := by
    intro t
    have hsplit : (∏ i ∈ Finset.univ \ t, -((0 : ℚ) ^ u i))
        = (∏ _i ∈ Finset.univ \ t, (-1 : ℚ)) * ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [Finset.prod_const_one, one_mul, prod_indicator_pow_sdiff, hsplit, Finset.prod_const,
      Finset.card_univ_sdiff, Fintype.card_fin]
  rw [← hl, key]
  exact Finset.sum_congr rfl fun t _ => (hr t).symm

/-- The `d`-fold mixed difference `∑_S (-1)^{d-|S|} P(1_S)` at the origin of a polynomial of total degree `≤ d`
is the coefficient of the monomial `n_1⋯n_d`. -/
theorem mixed_difference_eq_coeff_of_totalDegree_le {d : ℕ} (P : MvPolynomial (Fin d) ℚ)
    (hP : P.totalDegree ≤ d) :
    (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P)
      = MvPolynomial.coeff (∑ i, Finsupp.single i 1) P := by
  classical
  set v : Fin d →₀ ℕ := ∑ i, Finsupp.single i 1 with hvdef
  have hvapp : ∀ j : Fin d, v j = 1 := by
    intro j
    simp [hvdef, Finset.sum_apply', Finsupp.single_apply]
  have hexp : (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P)
      = ∑ u ∈ P.support, P.coeff u * ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) := by
    calc (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
            MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P)
        = ∑ S : Finset (Fin d), ∑ u ∈ P.support, P.coeff u *
            ((-1 : ℚ) ^ (d - S.card) *
              ∏ i : Fin d, (if i ∈ S then (1 : ℚ) else 0) ^ u i) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [MvPolynomial.eval_eq', Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring
      _ = ∑ u ∈ P.support, ∑ S : Finset (Fin d), P.coeff u *
            ((-1 : ℚ) ^ (d - S.card) *
              ∏ i : Fin d, (if i ∈ S then (1 : ℚ) else 0) ^ u i) := Finset.sum_comm
      _ = ∑ u ∈ P.support, P.coeff u * ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.mul_sum, alternating_sum_indicator_prod_eq]
  have hone : ∀ w : Fin d →₀ ℕ, (∀ i, w i ≠ 0) →
      (∏ i : Fin d, (1 - (0 : ℚ) ^ w i)) = 1 :=
    fun w hw => Finset.prod_eq_one fun i _ => by rw [zero_pow (hw i), sub_zero]
  have hzero : ∀ (w : Fin d →₀ ℕ) (j : Fin d), w j = 0 →
      (∏ i : Fin d, (1 - (0 : ℚ) ^ w i)) = 0 :=
    fun w j hj => Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, pow_zero, sub_self])
  have hstep : (∑ u ∈ P.support, P.coeff u * ∏ i : Fin d, (1 - (0 : ℚ) ^ u i))
      = P.coeff v * ∏ i : Fin d, (1 - (0 : ℚ) ^ v i) := by
    refine Finset.sum_eq_single v ?_ ?_
    · intro u hu hne
      by_cases h : ∀ i, u i ≠ 0
      · exfalso
        refine hne ?_
        have hsupp : u.support = (Finset.univ : Finset (Fin d)) := by
          ext i
          simp only [Finsupp.mem_support_iff, Finset.mem_univ, iff_true]
          exact h i
        have hle : (∑ i : Fin d, u i) ≤ d := by
          have h1 := le_trans (MvPolynomial.le_totalDegree hu) hP
          rwa [Finsupp.sum, hsupp] at h1
        have hcst : (∑ _i : Fin d, (1 : ℕ)) = d := by simp
        have hge : (∑ _i : Fin d, (1 : ℕ)) ≤ ∑ i : Fin d, u i :=
          Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (h i)
        have heq : (∑ _i : Fin d, (1 : ℕ)) = ∑ i : Fin d, u i := by omega
        have hall := (Finset.sum_eq_sum_iff_of_le
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
            Nat.one_le_iff_ne_zero.mpr (h i))).mp heq
        refine Finsupp.ext fun i => ?_
        rw [hvapp i]
        exact (hall i (Finset.mem_univ i)).symm
      · push Not at h
        obtain ⟨j, hj⟩ := h
        rw [hzero u j hj, mul_zero]
    · intro hv
      have : P.coeff v = 0 := by
        by_contra hc
        exact hv (MvPolynomial.mem_support_iff.mpr hc)
      rw [this, zero_mul]
  rw [hexp, hstep, hone v (fun i => by rw [hvapp i]; exact one_ne_zero), mul_one]

/-- **Main lemma**: the `(d+1)`-fold mixed difference of a polynomial in `d+1` variables of total degree `≤ d`
vanishes. -/
theorem mixed_difference_eq_zero_of_totalDegree_le {d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℚ)
    (hP : P.totalDegree ≤ d) :
    (∑ S : Finset (Fin (d + 1)), (-1 : ℚ) ^ (d + 1 - S.card) *
        MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P) = 0 := by
  classical
  rw [mixed_difference_eq_coeff_of_totalDegree_le P (Nat.le_succ_of_le hP)]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  have hv : ∀ j : Fin (d + 1), (∑ i : Fin (d + 1), Finsupp.single i (1 : ℕ)) j = 1 := by
    intro j
    simp [Finset.sum_apply', Finsupp.single_apply]
  have hs : (∑ i : Fin (d + 1), Finsupp.single i (1 : ℕ)).support = Finset.univ := by
    ext j
    simp [Finsupp.mem_support_iff, hv j]
  rw [hs]
  simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

end MvPolynomial


/-! ## Splitting a sum over `Finset (Fin (d+1))`

`∑_{S ⊆ Fin (d+1)} f S = ∑_{T ⊆ Fin d} (f (T.map succ) + f (insert 0 (T.map succ)))`:
group by whether `0 ∈ S` (`Fin.univ_succ` + `Finset.sum_powerset_insert` + `Finset.powerset_image`). -/

namespace Finset

theorem sum_finset_fin_succ_split {d : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Finset (Fin (d + 1)) → M) :
    (∑ S : Finset (Fin (d + 1)), f S)
      = ∑ T : Finset (Fin d), (f (T.map (Fin.succEmb d)) + f (insert 0 (T.map (Fin.succEmb d)))) := by
  classical
  have h0 : (0 : Fin (d + 1)) ∉
      (Finset.univ : Finset (Fin d)).map ⟨Fin.succ, Fin.succ_injective d⟩ := by
    simp [Finset.mem_map, Fin.succ_ne_zero]
  rw [← Finset.powerset_univ, Fin.univ_succ, Finset.cons_eq_insert, Finset.sum_powerset_insert h0,
    ← Finset.sum_add_distrib]
  rw [Finset.map_eq_image, Finset.powerset_image]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_image (Finset.image_injOn_powerset_of_injOn (Fin.succ_injective d).injOn),
    Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp [Finset.map_eq_image]

theorem card_le_of_fin {d : ℕ} (T : Finset (Fin d)) : T.card ≤ d := by
  simpa using Finset.card_le_univ T

end Finset

end
