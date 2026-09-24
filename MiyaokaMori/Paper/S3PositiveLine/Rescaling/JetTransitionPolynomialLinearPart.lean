import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Charts.TransitionPolynomial

/-! # Linear part of a weighted-homogeneous polynomial and the jet transition polynomial
(helper for the jet transition, §2 of the paper)

Pure `MvPolynomial` algebra behind `affineJetCoord_jetTransitionRelated`
(`AffineJetChartTransition`):

* `linearPart` is the library's `MiyaokaMori.JetTransition.linearPart`; `linearPart_eq_sum` gives
  `linearPart T = Σ_j C (coeff (X_j) T) X_j` for finite `σ`; for `T` with zero constant term the remainder
  `T - linearPart T` lies in `(x)²` (`sub_linearPart_mem_sq`, the private
  `linearRemainder_mem_square` of `JetTransition` for an arbitrary finite variable set).
* The degree-one coefficient of a product (`coeff_single_one_mul`), vanishes on `(x)²`, and the
  **linear part of a substitution**: for `T`, `T'_j` without constant terms,
  `coeff_{X_k} (T[x ↦ T']) = Σ_j coeff_{X_j} T · coeff_{X_k} T'_j` (`coeff_single_one_bind₁`) — "the
  linear parts compose".
* For the jet weights `w (i, q) = q + 1`: a weighted-homogeneous `T` of weight `q + 1` splits as
  `linearPart T + P` with `P` a jet transition polynomial (`isJetTransitionPolynomial_sub_linearPart`),
  `linearPart T` only involving the variables `X_{(j, q)}` (`coeff_single_one_eq_zero_of_ne`);
  `IsJetTransitionPolynomial` is stable under coefficient maps (`isJetTransitionPolynomial_map`).
* `matrix_mul_eq_one_of_bind₁_eq_X`: if two families of weighted-homogeneous polynomials are
  inverse substitutions on the weight-`(q+1)` variables, their linear-part matrices multiply to `1`.
* `eval₂_eq_sum_linear_add_eval₂_sub_linearPart`: evaluating a weight-`(q+1)` polynomial `T` at a
  tuple `b` gives `Σ_j θ (coeff_{X_{(j,q)}} T) · b (j, q) + eval₂ θ b (T - linearPart T)` — the shape
  of one line of (2.7).
* `isWeightedHomogeneous_rename_of_injective`: weighted homogeneity is transported along an injective
  renaming of the variables (used to pass from the `ULift`-indexed honesty presentation to
  `Fin (n+1) × Fin κ`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace JetChartTransitionPoly

open MiyaokaMori.JetTransition (linearPart)

open MvPolynomial

section General

variable {R : Type*} [CommRing R] {σ : Type*}

-- The linear part is `MiyaokaMori.JetTransition.linearPart` (support-based, any `σ`); the sum formula
-- `Σ_j C (coeff (X_j) T) · X_j` for finite `σ` is the theorem `linearPart_eq_sum`.
/-- For a finite variable set the linear part is `Σ_j C (coeff (X_j) T) · X_j`
(coefficientwise from `MiyaokaMori.JetTransition.coeff_linearPart`: the exponents of degree one are
exactly the `single j 1`). -/
theorem linearPart_eq_sum [Fintype σ] (T : MvPolynomial σ R) :
    linearPart T = ∑ j, C (T.coeff (Finsupp.single j 1)) * X j := by
  classical
  ext d
  rw [MiyaokaMori.JetTransition.coeff_linearPart, coeff_sum]
  simp only [coeff_C_mul, coeff_X]
  by_cases hd : d.degree = 1
  · have hmem : d ∈ Set.range (fun i : σ ↦ Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]; exact hd
    obtain ⟨i, rfl⟩ := hmem
    rw [if_pos hd, Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one]
    · intro j _ hj
      rw [if_neg, mul_zero]
      exact fun h => hj ((Finsupp.single_left_injective (M := ℕ) one_ne_zero) h)
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hd]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg, mul_zero]
    intro h
    apply hd
    rw [← h, Finsupp.degree_single]

theorem coeff_single_one_linearPart [Fintype σ] (T : MvPolynomial σ R) (j : σ) :
    (linearPart T).coeff (Finsupp.single j 1) = T.coeff (Finsupp.single j 1) := by
  classical
  rw [linearPart_eq_sum]
  rw [coeff_sum, Finset.sum_eq_single j]
  · rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one]
  · intro b _ hb
    rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
    exact fun h => hb ((Finsupp.single_left_injective (M := ℕ) one_ne_zero) h)
  · intro h; exact absurd (Finset.mem_univ j) h

theorem coeff_zero_linearPart [Fintype σ] (T : MvPolynomial σ R) :
    (linearPart T).coeff 0 = 0 := by
  classical
  rw [linearPart_eq_sum]
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_C_mul, coeff_X, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), mul_zero]

theorem eval₂_linearPart [Fintype σ] {K : Type*} [CommRing K] (θ : R →+* K) (a : σ → K)
    (T : MvPolynomial σ R) :
    eval₂ θ a (linearPart T) = ∑ j, θ (T.coeff (Finsupp.single j 1)) * a j := by
  rw [linearPart_eq_sum]
  rw [eval₂_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [eval₂_mul, eval₂_C, eval₂_X]

/-- A polynomial without constant term minus its linear part lies in `(x)²`
(`JetTransition`, `linearRemainder_mem_square`, for an arbitrary finite variable set). -/
theorem sub_linearPart_mem_sq [Fintype σ] (T : MvPolynomial σ R) (h0 : T.coeff 0 = 0) :
    T - linearPart T ∈ idealOfVars σ R ^ 2 := by
  classical
  rw [mem_pow_idealOfVars_iff]
  intro m hm
  by_contra hdegree
  have hle : m.degree ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hdeg | hdeg
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hdeg
    subst m
    rw [mem_support_iff, coeff_sub, h0, coeff_zero_linearPart, sub_zero] at hm
    exact hm rfl
  · have hmrange : m ∈ Set.range (fun i : σ ↦ Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact hdeg
    obtain ⟨i, rfl⟩ := hmrange
    rw [mem_support_iff, coeff_sub, coeff_single_one_linearPart, sub_self] at hm
    exact hm rfl

/-- The degree-one coefficient is `constantCoeff ∘ pderiv`. -/
theorem coeff_single_one_eq_constantCoeff_pderiv (p : MvPolynomial σ R) (k : σ) :
    p.coeff (Finsupp.single k 1) = constantCoeff (pderiv k p) := by
  rw [constantCoeff_eq, coeff_pderiv, zero_add]
  simp

/-- Product rule for the degree-one coefficient. -/
theorem coeff_single_one_mul (a b : MvPolynomial σ R) (k : σ) :
    (a * b).coeff (Finsupp.single k 1) =
      a.coeff 0 * b.coeff (Finsupp.single k 1) + a.coeff (Finsupp.single k 1) * b.coeff 0 := by
  simp only [coeff_single_one_eq_constantCoeff_pderiv, pderiv_mul, map_add, map_mul]
  change _ = constantCoeff a * _ + _ * constantCoeff b
  ring

theorem coeff_zero_eq_zero_of_mem_idealOfVars {p : MvPolynomial σ R} (hp : p ∈ idealOfVars σ R) :
    p.coeff 0 = 0 := by
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff] at hp
  by_contra h
  have := hp 0 (mem_support_iff.mpr h)
  simp at this

/-- The degree-one coefficients vanish on `(x)²`. -/
theorem coeff_single_one_eq_zero_of_mem_sq {p : MvPolynomial σ R} (hp : p ∈ idealOfVars σ R ^ 2)
    (k : σ) : p.coeff (Finsupp.single k 1) = 0 := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp ?_ ?_
  · intro a ha b hb
    rw [coeff_single_one_mul, coeff_zero_eq_zero_of_mem_idealOfVars ha,
      coeff_zero_eq_zero_of_mem_idealOfVars hb, zero_mul, mul_zero, add_zero]
  · intro x y hx hy
    rw [coeff_add, hx, hy, add_zero]

/-- A substitution by polynomials without constant term preserves `(x)²`. -/
theorem bind₁_mem_sq (T' : σ → MvPolynomial σ R) (hT' : ∀ j, (T' j).coeff 0 = 0)
    {P : MvPolynomial σ R} (hP : P ∈ idealOfVars σ R ^ 2) :
    bind₁ T' P ∈ idealOfVars σ R ^ 2 := by
  have hmap : Ideal.map (bind₁ T').toRingHom (idealOfVars σ R) ≤ idealOfVars σ R := by
    rw [Ideal.map_le_iff_le_comap]
    rw [show idealOfVars σ R = Ideal.span (Set.range MvPolynomial.X) from rfl, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change bind₁ T' (X i) ∈ idealOfVars σ R
    rw [bind₁_X_right, ← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
    intro m hm
    by_contra hdeg
    have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    subst hm0
    exact (mem_support_iff.mp hm) (hT' i)
  have hpmap : bind₁ T' P ∈ Ideal.map (bind₁ T').toRingHom (idealOfVars σ R ^ 2) :=
    Ideal.mem_map_of_mem (bind₁ T').toRingHom hP
  rw [Ideal.map_pow, pow_two] at hpmap
  rw [pow_two]
  exact Ideal.mul_mono hmap hmap hpmap

/-- **The linear parts compose**: for `T` and all `T'_j` without constant term,
`coeff_{X_k} (T[x ↦ T']) = Σ_j coeff_{X_j} T · coeff_{X_k} T'_j`. -/
theorem coeff_single_one_bind₁ [Fintype σ] (T' : σ → MvPolynomial σ R)
    (hT' : ∀ j, (T' j).coeff 0 = 0) (T : MvPolynomial σ R) (hT : T.coeff 0 = 0) (k : σ) :
    (bind₁ T' T).coeff (Finsupp.single k 1) =
      ∑ j, T.coeff (Finsupp.single j 1) * (T' j).coeff (Finsupp.single k 1) := by
  have hsplit : T = linearPart T + (T - linearPart T) := by ring
  conv_lhs => rw [hsplit]
  rw [map_add, coeff_add, coeff_single_one_eq_zero_of_mem_sq (bind₁_mem_sq T' hT'
    (sub_linearPart_mem_sq T hT)) k, add_zero]
  rw [linearPart_eq_sum]
  rw [map_sum, coeff_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, bind₁_C_right, bind₁_X_right, coeff_C_mul]

/-- Weighted homogeneity is transported along an injective renaming of the variables:
`rename f φ` is `w`-homogeneous of weight `m` when `φ` is `(w ∘ f)`-homogeneous of weight `m`
(`support_rename_of_injective`, `Finsupp.linearCombination_mapDomain`). -/
theorem isWeightedHomogeneous_rename_of_injective {τ : Type*} {w : τ → ℕ} {m : ℕ}
    {φ : MvPolynomial σ R} {f : σ → τ} (hf : Function.Injective f)
    (h : φ.IsWeightedHomogeneous (w ∘ f) m) : (rename f φ).IsWeightedHomogeneous w m := by
  classical
  intro d hd
  have hd' : d ∈ (rename f φ).support := mem_support_iff.mpr hd
  rw [support_rename_of_injective hf, Finset.mem_image] at hd'
  obtain ⟨d', hd', rfl⟩ := hd'
  rw [← h (mem_support_iff.mp hd')]
  exact Finsupp.linearCombination_mapDomain (R := ℕ) (v' := w) f d'

end General

/-! ## The jet weights `w (i, q) = q + 1` -/

section Jet

variable {R : Type*} [CommRing R] {n κ : ℕ}

/-- The jet weights: the variable `x_{i,q}` (with `q : Fin κ` counted from `0`) has weight `q + 1`,
as in `IsJetTransitionPolynomial`. -/
abbrev jetWt (n κ : ℕ) : Fin (n + 1) × Fin κ → ℕ := fun iq => (iq.2 : ℕ) + 1

theorem jetWt_ne_zero (p : Fin (n + 1) × Fin κ) : jetWt n κ p ≠ 0 := Nat.succ_ne_zero _

theorem weight_single_one (p : Fin (n + 1) × Fin κ) :
    Finsupp.weight (jetWt n κ) (Finsupp.single p 1) = jetWt n κ p := by
  rw [Finsupp.weight_single, one_smul]

/-- A weighted-homogeneous polynomial of positive weight has no constant term. -/
theorem coeff_zero_eq_zero_of_isWeightedHomogeneous {T : MvPolynomial (Fin (n + 1) × Fin κ) R}
    {m : ℕ} (hT : T.IsWeightedHomogeneous (jetWt n κ) m) (hm : m ≠ 0) : T.coeff 0 = 0 :=
  hT.coeff_eq_zero 0 (by rw [map_zero]; exact fun h => hm h.symm)

/-- Only the variables of weight `m` appear in the linear part of a weighted-homogeneous
polynomial of weight `m`. -/
theorem coeff_single_one_eq_zero_of_ne {T : MvPolynomial (Fin (n + 1) × Fin κ) R} {m : ℕ}
    (hT : T.IsWeightedHomogeneous (jetWt n κ) m) (p : Fin (n + 1) × Fin κ)
    (hp : jetWt n κ p ≠ m) : T.coeff (Finsupp.single p 1) = 0 :=
  hT.coeff_eq_zero _ (by rw [weight_single_one]; exact hp)

theorem isWeightedHomogeneous_linearPart {T : MvPolynomial (Fin (n + 1) × Fin κ) R} {m : ℕ}
    (hT : T.IsWeightedHomogeneous (jetWt n κ) m) :
    (linearPart T).IsWeightedHomogeneous (jetWt n κ) m := by
  rw [linearPart_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun p _ => ?_
  by_cases hp : jetWt n κ p = m
  · have h := (isWeightedHomogeneous_C (jetWt n κ) (T.coeff (Finsupp.single p 1))).mul
      (isWeightedHomogeneous_X R (jetWt n κ) p)
    rwa [zero_add, hp] at h
  · rw [coeff_single_one_eq_zero_of_ne hT p hp, map_zero, zero_mul]
    exact isWeightedHomogeneous_zero _ _ _

/-- `JetTransition`, `variable_weight_lt_of_degree_ge_two` (private there): a variable of a
monomial of degree `≥ 2` has weight strictly less than the monomial (positive weights). -/
theorem variable_weight_lt_of_two_le_degree {τ : Type*} (w : τ → ℕ) (hw : ∀ i, w i ≠ 0)
    (m : τ →₀ ℕ) (hm : 2 ≤ m.degree) {i : τ} (hi : i ∈ m.support) : w i < Finsupp.weight w m := by
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

/-- **Weighted-homogeneous = linear part + jet transition polynomial**
(§2.1–2.2 of the paper, (2.7)): if `T` is weighted homogeneous of weight `q + 1` for
the jet weights, then `T - linearPart T` is a jet transition polynomial of weight `q + 1`: it is
weighted homogeneous, all its monomials have degree `≥ 2` (`sub_linearPart_mem_sq`), and every
variable occurring in such a monomial has weight `< q + 1`
(`variable_weight_lt_of_two_le_degree`). -/
theorem isJetTransitionPolynomial_sub_linearPart (q : Fin κ)
    {T : MvPolynomial (Fin (n + 1) × Fin κ) R}
    (hT : T.IsWeightedHomogeneous (jetWt n κ) ((q : ℕ) + 1)) :
    IsJetTransitionPolynomial n κ ((q : ℕ) + 1) (T - linearPart T) := by
  have hhom : (T - linearPart T).IsWeightedHomogeneous (jetWt n κ) ((q : ℕ) + 1) :=
    hT.sub (isWeightedHomogeneous_linearPart hT)
  have hsq := sub_linearPart_mem_sq T
    (coeff_zero_eq_zero_of_isWeightedHomogeneous hT (Nat.succ_ne_zero _))
  rw [mem_pow_idealOfVars_iff] at hsq
  refine ⟨hhom, fun m hm => hsq m hm, fun m hm iq hiq => ?_⟩
  have hw := variable_weight_lt_of_two_le_degree (jetWt n κ) jetWt_ne_zero m (hsq m hm) hiq
  rw [hhom (mem_support_iff.mp hm)] at hw
  exact hw

/-- `IsJetTransitionPolynomial` is preserved by a coefficient map. -/
theorem isJetTransitionPolynomial_map {R' : Type*} [CommRing R'] (φ : R →+* R') {q : ℕ}
    {P : MvPolynomial (Fin (n + 1) × Fin κ) R} (h : IsJetTransitionPolynomial n κ q P) :
    IsJetTransitionPolynomial n κ q (map φ P) := by
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m hm iq hiq => ?_⟩
  · rw [coeff_map] at hm
    exact h.weighted_homogeneous fun h0 => hm (by rw [h0, map_zero])
  · exact h.degree_ge_two m (support_map_subset _ _ hm)
  · exact h.lower_order m (support_map_subset _ _ hm) iq hiq

/-- **The linear-part matrices of inverse substitutions are inverse** (the "inverse transition"
of Lemma 3.1 of the paper): let `T p`, `T' p` be weighted homogeneous of weight `w p` and
`T (i, q)[x ↦ T'] = X (i, q)` for every `i`. Then the matrices `g i j = coeff_{X_{(j,q)}} T (i, q)`
and `g' j k = coeff_{X_{(k,q)}} T' (j, q)` satisfy `g * g' = 1`. Proof: read the coefficient of
`X_{(k,q)}` in `T (i, q)[x ↦ T']` with `coeff_single_one_bind₁`; the terms with a variable of
weight `≠ q + 1` vanish (`coeff_single_one_eq_zero_of_ne`). -/
theorem matrix_mul_eq_one_of_bind₁_eq_X (q : Fin κ)
    (T T' : Fin (n + 1) × Fin κ → MvPolynomial (Fin (n + 1) × Fin κ) R)
    (hT : ∀ p, (T p).IsWeightedHomogeneous (jetWt n κ) (jetWt n κ p))
    (hT' : ∀ p, (T' p).IsWeightedHomogeneous (jetWt n κ) (jetWt n κ p))
    (h : ∀ i : Fin (n + 1), bind₁ T' (T (i, q)) = X (i, q)) :
    (Matrix.of fun i j : Fin (n + 1) => (T (i, q)).coeff (Finsupp.single (j, q) 1)) *
      (Matrix.of fun j k : Fin (n + 1) => (T' (j, q)).coeff (Finsupp.single (k, q) 1)) = 1 := by
  classical
  refine Matrix.ext fun i k => ?_
  have hsum : (∑ j : Fin (n + 1) × Fin κ, (T (i, q)).coeff (Finsupp.single j 1) *
      (T' j).coeff (Finsupp.single (k, q) 1)) =
      ∑ j : Fin (n + 1), (T (i, q)).coeff (Finsupp.single (j, q) 1) *
        (T' (j, q)).coeff (Finsupp.single (k, q) 1) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single q]
    · intro q' _ hq'
      rw [coeff_single_one_eq_zero_of_ne (hT (i, q)) (j, q') (by
        show (q' : ℕ) + 1 ≠ (q : ℕ) + 1
        exact fun h => hq' (Fin.ext (Nat.succ_injective h))), zero_mul]
    · intro h; exact absurd (Finset.mem_univ q) h
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ j : Fin (n + 1), (T (i, q)).coeff (Finsupp.single (j, q) 1) *
    (T' (j, q)).coeff (Finsupp.single (k, q) 1)) = (if i = k then 1 else 0)
  rw [← hsum, ← coeff_single_one_bind₁ T' (fun j => coeff_zero_eq_zero_of_isWeightedHomogeneous
    (hT' j) (jetWt_ne_zero j)) _ (coeff_zero_eq_zero_of_isWeightedHomogeneous (hT (i, q))
    (jetWt_ne_zero _)), h i, coeff_X]
  by_cases hik : i = k
  · subst hik; simp
  · rw [if_neg hik, if_neg]
    intro h
    exact hik (Prod.ext_iff.mp ((Finsupp.single_left_injective (M := ℕ) one_ne_zero) h)).1

/-- For `T` weighted homogeneous of weight `q + 1`, the linear part evaluates to the sum over the
weight-`(q+1)` variables `X_{(j,q)}` only (`coeff_single_one_eq_zero_of_ne`). -/
theorem eval₂_linearPart_of_isWeightedHomogeneous {K : Type*} [CommRing K] (θ : R →+* K)
    (b : Fin (n + 1) × Fin κ → K) (q : Fin κ) {T : MvPolynomial (Fin (n + 1) × Fin κ) R}
    (hT : T.IsWeightedHomogeneous (jetWt n κ) ((q : ℕ) + 1)) :
    eval₂ θ b (linearPart T) =
      ∑ j : Fin (n + 1), θ (T.coeff (Finsupp.single (j, q) 1)) * b (j, q) := by
  classical
  rw [eval₂_linearPart, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single q]
  · intro q' _ hq'
    rw [coeff_single_one_eq_zero_of_ne hT (j, q') (by
      show (q' : ℕ) + 1 ≠ (q : ℕ) + 1
      exact fun h => hq' (Fin.ext (Nat.succ_injective h))), map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ q) h

/-- **One line of (2.7)** (§2.1–2.2 of the paper): evaluating a weight-`(q+1)`
polynomial `T` at `b` is the linear combination `Σ_j θ (coeff_{X_{(j,q)}} T) · b (j, q)` of the
weight-`(q+1)` coordinates plus the value of the jet transition polynomial `T - linearPart T`
(`isJetTransitionPolynomial_sub_linearPart`). -/
theorem eval₂_eq_sum_linear_add_eval₂_sub_linearPart {K : Type*} [CommRing K] (θ : R →+* K)
    (b : Fin (n + 1) × Fin κ → K) (q : Fin κ) {T : MvPolynomial (Fin (n + 1) × Fin κ) R}
    (hT : T.IsWeightedHomogeneous (jetWt n κ) ((q : ℕ) + 1)) :
    eval₂ θ b T =
      (∑ j : Fin (n + 1), θ (T.coeff (Finsupp.single (j, q) 1)) * b (j, q)) +
        eval₂ θ b (T - linearPart T) := by
  rw [eval₂_sub, ← eval₂_linearPart_of_isWeightedHomogeneous θ b q hT]
  ring

end Jet

end JetChartTransitionPoly

end
