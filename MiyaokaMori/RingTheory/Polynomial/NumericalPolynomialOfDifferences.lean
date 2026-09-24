import MiyaokaMori.Prelude

/-! # Numerical polynomials from their differences

The difference criterion (the "simple arithmetic argument" at the end of Stacks 0BEM): if `P : ℤ^r → ℚ` is
such that for every `i` the difference `P(n + e_i) − P(n)` is given by a rational polynomial of total degree
`< e`, then `P` itself is given by a rational polynomial of total degree `≤ e`.

Reference: Stacks 0BEM (end of the proof).

## Proof

Induction on the number of variables `r`. The polynomial-level tools are the shift operator
`shiftX i := bind₁ (update X i (X i + 1))` and the difference operator `Dop i := shiftX i - id`
on `MvPolynomial (Fin r) ℚ`.

* `Dop_X_pow_mul_monomial`: for `b i = 0`,
  `Dop i (X i ^ k * monomial b 1) = ∑ m < k, C(k, m) • X i ^ m * monomial b 1` (binomial theorem).
* `exists_Dop_eq_of_degLt` (discrete antiderivative): every `Q` with `Q = 0` or
  `totalDegree Q < e` is `Dop i S` for some `S` of total degree `≤ e`. Proof: the set of such `Q`
  is the submodule `(restrictTotalDegree e).map (Dop i)`, so it suffices to treat the monomials
  `X i ^ k * monomial b 1` with `k + |b| < e`; strong induction on `k` using
  `Dop i (X i ^ (k+1) M) = (k+1) • X i ^ k M + (lower powers of X i)`.
* `Dop_mem_degLtSubmodule`: if `totalDegree S ≤ e` then `Dop i S = 0 ∨ totalDegree (Dop i S) < e`
  (each monomial loses at least one degree).

Induction step (`r + 1` variables): choose `S` with `Dop 0 S = Q₀` (`Q₀` the difference polynomial
in direction `0`); then `F := P - eval S` is invariant under the shift `n ↦ n + e₀`, so
`F n = F (Fin.cons 0 (Fin.tail n))` (walk along the first coordinate, `Int.induction_on`). The
function `P' n' := F (Fin.cons 0 n')` on `ℤ^r` has differences `eval (Fin.cons 0 n') (Q_j - Dop j S)`,
and restricting to `x₀ = 0` is `(finSuccEquiv ℚ r ·).coeff 0`, which does not raise the total degree
(`totalDegree_coeff_finSuccEquiv_add_le`). By induction `P' = eval R'`, and `R := S + rename Fin.succ R'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Finset

noncomputable section

namespace MvPolynomial

namespace NumericalPolynomialOfDifferences

variable {r : ℕ}

/-- The shift `x_i ↦ x_i + 1` as an algebra endomorphism of `ℚ[x_0, …, x_{r-1}]`. -/
def shiftX (i : Fin r) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] MvPolynomial (Fin r) ℚ :=
  bind₁ (Function.update (X : Fin r → MvPolynomial (Fin r) ℚ) i (X i + 1))

/-- The difference operator `p ↦ p(x + e_i) - p(x)` as a `ℚ`-linear map. -/
def Dop (i : Fin r) : MvPolynomial (Fin r) ℚ →ₗ[ℚ] MvPolynomial (Fin r) ℚ :=
  (shiftX i).toLinearMap - LinearMap.id

theorem Dop_apply (i : Fin r) (p : MvPolynomial (Fin r) ℚ) : Dop i p = shiftX i p - p := rfl

theorem eval_shiftX (i : Fin r) (p : MvPolynomial (Fin r) ℚ) (x : Fin r → ℚ) :
    eval x (shiftX i p) = eval (Function.update x i (x i + 1)) p := by
  have hfun : (fun j => eval₂Hom (RingHom.id ℚ) x
      (Function.update (X : Fin r → MvPolynomial (Fin r) ℚ) i (X i + 1) j)) =
      Function.update x i (x i + 1) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [Function.update_of_ne hj]
  show eval₂Hom (RingHom.id ℚ) x (bind₁ _ p) = eval₂Hom (RingHom.id ℚ) _ p
  rw [eval₂Hom_bind₁, hfun]

theorem eval_Dop (i : Fin r) (p : MvPolynomial (Fin r) ℚ) (x : Fin r → ℚ) :
    eval x (Dop i p) = eval (Function.update x i (x i + 1)) p - eval x p := by
  rw [Dop_apply, map_sub, eval_shiftX]

theorem shiftX_monomial_of_apply_eq_zero (i : Fin r) (b : Fin r →₀ ℕ) (hb : b i = 0) :
    shiftX i (monomial b 1) = monomial b 1 := by
  rw [shiftX, bind₁_monomial, monomial_eq, Finsupp.prod]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := by
    rintro rfl
    exact (Finsupp.mem_support_iff.1 hj) hb
  rw [Function.update_of_ne hji]

/-- The binomial expansion of the difference of `X i ^ k * monomial b 1` (with `b i = 0`). -/
theorem Dop_X_pow_mul_monomial (i : Fin r) (k : ℕ) (b : Fin r →₀ ℕ) (hb : b i = 0) :
    Dop i (X i ^ k * monomial b 1) =
      ∑ m ∈ range k, ((k.choose m : ℕ) : ℚ) • (X i ^ m * monomial b 1) := by
  rw [Dop_apply, map_mul, map_pow, shiftX_monomial_of_apply_eq_zero i b hb, shiftX, bind₁_X_right,
    Function.update_self, add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one,
    Nat.sub_self, pow_zero, mul_one, add_mul, Finset.sum_mul, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_pow, mul_one, smul_eq_C_mul, ← map_natCast C]
  ring

theorem totalDegree_X_pow_mul_monomial (i : Fin r) (k : ℕ) (b : Fin r →₀ ℕ) :
    (X i ^ k * monomial b 1 : MvPolynomial (Fin r) ℚ).totalDegree ≤ k + b.sum fun _ n => n :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_X_pow, totalDegree_monomial _ one_ne_zero])

theorem sum_single_add (i : Fin r) (k : ℕ) (b : Fin r →₀ ℕ) :
    ((Finsupp.single i k + b).sum fun _ n => n) = k + b.sum fun _ n => n := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

/-- The submodule of polynomials all of whose monomials have degree `< e`; equivalently
(`mem_degLtSubmodule_iff`) `p = 0 ∨ p.totalDegree < e`. -/
def degLtSubmodule (r e : ℕ) : Submodule ℚ (MvPolynomial (Fin r) ℚ) where
  carrier := {p | ∀ m ∈ p.support, (m.sum fun _ n => n) < e}
  add_mem' := by
    intro p q hp hq m hm
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hp m h
    · exact hq m h
  zero_mem' := by simp
  smul_mem' := fun c p hp m hm => hp m (support_smul hm)

theorem mem_degLtSubmodule_iff {e : ℕ} (p : MvPolynomial (Fin r) ℚ) :
    p ∈ degLtSubmodule r e ↔ p = 0 ∨ p.totalDegree < e := by
  constructor
  · intro h
    by_cases hp : p = 0
    · exact Or.inl hp
    · right
      obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hp)
      have he : 0 < e := (Nat.zero_le _).trans_lt (h m hm)
      rw [totalDegree, Finset.sup_lt_iff (by simpa using he)]
      exact h
  · rintro (rfl | h) m hm
    · simp at hm
    · exact (le_totalDegree hm).trans_lt h

theorem monomial_mem_degLtSubmodule {e : ℕ} (a : Fin r →₀ ℕ) (c : ℚ)
    (ha : (a.sum fun _ n => n) < e) : monomial a c ∈ degLtSubmodule r e := by
  intro m hm
  rw [support_monomial] at hm
  split_ifs at hm
  · simp at hm
  · rw [Finset.mem_singleton] at hm
    subst hm
    exact ha

/-- Difference lowers the total degree: if `totalDegree S ≤ e` then `Dop i S` is zero or has
total degree `< e`. -/
theorem Dop_mem_degLtSubmodule (i : Fin r) {e : ℕ} (S : MvPolynomial (Fin r) ℚ)
    (hS : S.totalDegree ≤ e) : Dop i S ∈ degLtSubmodule r e := by
  rw [S.as_sum, map_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hdeg : (a.sum fun _ n => n) ≤ e := (le_totalDegree ha).trans hS
  have hmon : monomial a (coeff a S) = coeff a S • monomial a 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul]
  refine Submodule.smul_mem _ _ ?_
  have hdeg' : a i + ((a.erase i).sum fun _ n => n) ≤ e := by
    rw [← sum_single_add, Finsupp.single_add_erase]; exact hdeg
  rw [← Finsupp.single_add_erase i a, monomial_single_add,
    Dop_X_pow_mul_monomial i _ _ Finsupp.erase_same]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ ?_
  rw [← monomial_single_add]
  refine monomial_mem_degLtSubmodule _ _ ?_
  rw [sum_single_add]
  have := Finset.mem_range.1 hm
  omega

/-- Discrete antiderivative of a monomial: for `b i = 0` and `k + |b| < e`, the monomial
`X i ^ k * monomial b 1` is `Dop i S` for some `S` of total degree `≤ e`. -/
theorem X_pow_mul_monomial_mem_map_Dop (i : Fin r) (e : ℕ) :
    ∀ (k : ℕ) (b : Fin r →₀ ℕ), b i = 0 → k + (b.sum fun _ n => n) < e →
      X i ^ k * monomial b 1 ∈ (restrictTotalDegree (Fin r) ℚ e).map (Dop i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro b hb hdeg
  set V := (restrictTotalDegree (Fin r) ℚ e).map (Dop i) with hV
  have hK := Dop_X_pow_mul_monomial i (k + 1) b hb
  rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at hK
  have h1 : Dop i (X i ^ (k + 1) * monomial b 1) ∈ V := by
    refine Submodule.mem_map_of_mem ?_
    rw [mem_restrictTotalDegree]
    exact (totalDegree_X_pow_mul_monomial i _ b).trans (by omega)
  have h2 : (∑ m ∈ range k, (((k + 1).choose m : ℕ) : ℚ) • (X i ^ m * monomial b 1)) ∈ V :=
    Submodule.sum_mem _ fun m hm =>
      Submodule.smul_mem _ _ (ih m (Finset.mem_range.1 hm) b hb (by have := Finset.mem_range.1 hm; omega))
  have h3 : (((k + 1 : ℕ) : ℚ)) • (X i ^ k * monomial b 1) ∈ V := by
    have := V.sub_mem h1 h2
    rwa [hK, add_sub_cancel_left] at this
  have h4 := V.smul_mem (((k + 1 : ℕ) : ℚ)⁻¹) h3
  rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h4

/-- Discrete antiderivative: every `Q` with `Q = 0 ∨ totalDegree Q < e` is `Dop i S` for some `S`
with `totalDegree S ≤ e`. -/
theorem exists_Dop_eq_of_degLt (i : Fin r) {e : ℕ} (Q : MvPolynomial (Fin r) ℚ)
    (hQ : Q = 0 ∨ Q.totalDegree < e) :
    ∃ S : MvPolynomial (Fin r) ℚ, S.totalDegree ≤ e ∧ Dop i S = Q := by
  suffices h : Q ∈ (restrictTotalDegree (Fin r) ℚ e).map (Dop i) by
    obtain ⟨S, hS, rfl⟩ := Submodule.mem_map.1 h
    exact ⟨S, (mem_restrictTotalDegree _ _ _).1 hS, rfl⟩
  rcases hQ with rfl | hQ
  · exact zero_mem _
  rw [Q.as_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hdeg : (a.sum fun _ n => n) < e := (le_totalDegree ha).trans_lt hQ
  have hmon : monomial a (coeff a Q) = coeff a Q • monomial a 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon]
  refine Submodule.smul_mem _ _ ?_
  have hdeg' : a i + ((a.erase i).sum fun _ n => n) < e := by
    rw [← sum_single_add, Finsupp.single_add_erase]; exact hdeg
  rw [← Finsupp.single_add_erase i a, monomial_single_add]
  exact X_pow_mul_monomial_mem_map_Dop i e _ _ Finsupp.erase_same hdeg'

/-- Walking along the first coordinate: a function on `ℤ^(r+1)` invariant under `n ↦ n + e₀`
depends only on the tail. -/
theorem eq_cons_zero_tail_of_shift_invariant (G : (Fin (r + 1) → ℤ) → ℚ)
    (hG : ∀ n, G (Function.update n 0 (n 0 + 1)) = G n) (n : Fin (r + 1) → ℤ) :
    G n = G (Fin.cons 0 (Fin.tail n)) := by
  have key : ∀ z : ℤ, G (Fin.cons z (Fin.tail n)) = G (Fin.cons 0 (Fin.tail n)) := by
    intro z
    induction z using Int.induction_on with
    | zero => rfl
    | succ k ih =>
      rw [← ih, ← hG (Fin.cons (k : ℤ) (Fin.tail n)), Fin.update_cons_zero, Fin.cons_zero]
    | pred k ih =>
      rw [← ih, ← hG (Fin.cons (-(k : ℤ) - 1) (Fin.tail n)), Fin.update_cons_zero, Fin.cons_zero,
        sub_add_cancel]
  conv_lhs => rw [← Fin.cons_self_tail n]
  exact key (n 0)

theorem cast_update (n : Fin r → ℤ) (i : Fin r) :
    (fun j => ((Function.update n i (n i + 1) j : ℤ) : ℚ)) =
      Function.update (fun j => (n j : ℚ)) i ((n i : ℚ) + 1) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

theorem cast_cons (n' : Fin r → ℤ) :
    (fun k => (((Fin.cons (0 : ℤ) n' : Fin (r + 1) → ℤ) k : ℤ) : ℚ)) =
      Fin.cons (0 : ℚ) (fun k => (n' k : ℚ)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp

theorem eval_cons_zero (x : Fin r → ℚ) (T : MvPolynomial (Fin (r + 1)) ℚ) :
    eval (Fin.cons 0 x) T = eval x ((finSuccEquiv ℚ r T).coeff 0) := by
  rw [eval_eq_eval_mv_eval', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]

theorem coeff_zero_finSuccEquiv_degLt {e : ℕ} (T : MvPolynomial (Fin (r + 1)) ℚ)
    (hT : T = 0 ∨ T.totalDegree < e) :
    (finSuccEquiv ℚ r T).coeff 0 = 0 ∨ ((finSuccEquiv ℚ r T).coeff 0).totalDegree < e := by
  rcases hT with rfl | hT
  · simp
  by_cases h0 : (finSuccEquiv ℚ r T).coeff 0 = 0
  · exact Or.inl h0
  · right
    have := totalDegree_coeff_finSuccEquiv_add_le T 0 h0
    omega

end NumericalPolynomialOfDifferences

end MvPolynomial

open MvPolynomial MvPolynomial.NumericalPolynomialOfDifferences in
theorem MvPolynomial.exists_eval_eq_of_forall_sub_eval_eq {r e : ℕ} (P : (Fin r → ℤ) → ℚ)
    (hP : ∀ i : Fin r, ∃ Q : MvPolynomial (Fin r) ℚ, (Q = 0 ∨ Q.totalDegree < e) ∧
      ∀ n : Fin r → ℤ, P (Function.update n i (n i + 1)) - P n = MvPolynomial.eval (fun j => (n j : ℚ)) Q) :
    ∃ R : MvPolynomial (Fin r) ℚ, R.totalDegree ≤ e ∧ ∀ n : Fin r → ℤ, P n = MvPolynomial.eval (fun j => (n j : ℚ)) R := by
  induction r with
  | zero =>
    refine ⟨C (P default), by simp, fun n => ?_⟩
    rw [eval_C, Subsingleton.elim n default]
  | succ r ih =>
    obtain ⟨Q₀, hQ₀, hdiff₀⟩ := hP 0
    obtain ⟨S, hS, hDS⟩ := exists_Dop_eq_of_degLt 0 Q₀ hQ₀
    set F : (Fin (r + 1) → ℤ) → ℚ := fun n => P n - eval (fun j => (n j : ℚ)) S with hF
    have hFshift : ∀ n, F (Function.update n 0 (n 0 + 1)) = F n := by
      intro n
      have h := hdiff₀ n
      rw [← hDS, eval_Dop, ← cast_update] at h
      simp only [hF]
      linarith
    set P' : (Fin r → ℤ) → ℚ := fun n' => F (Fin.cons 0 n') with hP'
    have hP'hyp : ∀ j : Fin r, ∃ Q' : MvPolynomial (Fin r) ℚ, (Q' = 0 ∨ Q'.totalDegree < e) ∧
        ∀ n' : Fin r → ℤ, P' (Function.update n' j (n' j + 1)) - P' n' =
          eval (fun k => (n' k : ℚ)) Q' := by
      intro j
      obtain ⟨Q, hQ, hdiff⟩ := hP j.succ
      have hT : Q - Dop j.succ S ∈ degLtSubmodule (r + 1) e :=
        (degLtSubmodule (r + 1) e).sub_mem ((mem_degLtSubmodule_iff Q).2 hQ)
          (Dop_mem_degLtSubmodule j.succ S hS)
      refine ⟨(finSuccEquiv ℚ r (Q - Dop j.succ S)).coeff 0,
        coeff_zero_finSuccEquiv_degLt _ ((mem_degLtSubmodule_iff _).1 hT), fun n' => ?_⟩
      have hN : (Fin.cons (0 : ℤ) (Function.update n' j (n' j + 1)) : Fin (r + 1) → ℤ) =
          Function.update (Fin.cons (0 : ℤ) n' : Fin (r + 1) → ℤ) j.succ
            ((Fin.cons (0 : ℤ) n' : Fin (r + 1) → ℤ) j.succ + 1) := by
        rw [Fin.cons_update, Fin.cons_succ]
      simp only [hP', hF]
      rw [hN, ← eval_cons_zero, ← cast_cons, map_sub, eval_Dop, ← cast_update, ← hdiff]
      ring
    obtain ⟨R', hR', hPR'⟩ := ih P' hP'hyp
    refine ⟨S + rename Fin.succ R', ?_, fun n => ?_⟩
    · exact (totalDegree_add _ _).trans (max_le hS ((totalDegree_rename_le _ _).trans hR'))
    · have h1 : F n = P' (Fin.tail n) := eq_cons_zero_tail_of_shift_invariant F hFshift n
      have h2 := hPR' (Fin.tail n)
      rw [map_add, eval_rename]
      have h3 : eval ((fun j => (n j : ℚ)) ∘ Fin.succ) R' =
          eval (fun k => ((Fin.tail n k : ℤ) : ℚ)) R' := rfl
      rw [h3, ← h2, ← h1]
      simp only [hF]
      ring

end
