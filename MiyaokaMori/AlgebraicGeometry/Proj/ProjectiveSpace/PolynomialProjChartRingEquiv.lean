import MiyaokaMori.Prelude

/-! # The chart ring equivalence of the polynomial Proj

**Statement.** Let `R` be a commutative ring, `σ` a type with decidable equality and `j : σ`. Give
`R[x_σ] = MvPolynomial σ R` the standard grading (all weights `1`, encoded as
`MvPolynomial.weightedHomogeneousSubmodule R (fun _ : σ => 1)`, the grading used by
`WeightedPolynomialAtlas` with `w = fun _ => 1`). Then the degree-zero homogeneous localisation
`(R[x_σ]_{x_j})_0 = HomogeneousLocalization.Away 𝒫 (X j)` (the coordinate ring of the standard chart
`D_+(x_j) ⊆ Proj R[x_σ]`) is isomorphic, as a ring, to the polynomial ring `R[y_k : k ≠ j]`, by
`y_k ↦ x_k / x_j` ("dehomogenisation"), and this isomorphism is compatible with the structure maps from `R`
(`chartRingEquiv_comp_fromZeroRingHom_comp_algebraMap`).

**Source.** Hartshorne II.2.5 (the proof of `Proj S` being a scheme: `D_+(f) ≅ Spec S_{(f)}`) and the
computation `k[x_0..x_N]_{(x_i)} = k[x_j/x_i : j ≠ i]` (Hartshorne II, Exercise 2.14 / Stacks 01NE, the
standard affine charts of `P^n_R`); the paper uses `Y_k^{GG}` locally `≅ U × P(w)` in Lemma 2.3.

**Proof.** Exactly the argument of `ProjectiveSpaceChartPolynomial`
(the special case `R` a field, `σ = Fin (N+1)`), with
`k` replaced by an arbitrary commutative ring `R` and `Fin (N + 1)` by `σ` — nothing in the argument uses the
field structure:
1. `chartToPoly : (R[x]_{x_j})_0 → R[y]` is the restriction to the degree-zero part of the localisation
   universal-property map `R[x][1/x_j] → R[y]` induced by dehomogenisation `x_j ↦ 1`, `x_k ↦ y_k`
   (`x_j` is sent to the unit `1`). On a fraction `a / x_j^n` it is `a(x_j := 1)` (`chartToPoly_mk`).
2. `polyToChart : R[y] → (R[x]_{x_j})_0` is `eval₂` sending `r ↦ r/1` and `y_k ↦ x_k / x_j`.
3. `chartToPoly ∘ polyToChart = id` on the generators `C r` and `y_k` (`MvPolynomial.ringHom_ext`).
4. `polyToChart ∘ chartToPoly = id`: every element is `a / x_j^n` with `a` homogeneous of degree `n`
   (`HomogeneousLocalization.Away.mk_surjective`); `polyToChart (a(x_j := 1))` has value
   `awayScale a := a(x_k := x_k / x_j)` in `R[x][1/x_j]` (`val_polyToChart_dehomogenize`), and for a
   homogeneous `a` of degree `n` this is `a / x_j^n` (`awayScale_of_isWeightedHomogeneous`, monomial by
   monomial: `x^α / x_j^{|α|}`).

Edge cases: `R` the zero ring — both sides are the zero ring and the statement is trivially true (the
argument never divides by anything); `σ = {j}` — `R[y_∅] = R` and `(R[x_j]_{x_j})_0 = R`, fine.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u v

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace MvPolynomial.StandardProjChart

variable (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (j : σ)

/-- The standard grading of `R[x_σ]` (all weights `1`), in the `weightedHomogeneousSubmodule` encoding. -/
abbrev grading : ℕ → Submodule R (MvPolynomial σ R) :=
  MvPolynomial.weightedHomogeneousSubmodule R (fun _ : σ => (1 : ℕ))

omit [DecidableEq σ] in
/-- `x_j` is homogeneous of degree `1`. -/
lemma X_mem : (MvPolynomial.X j : MvPolynomial σ R) ∈ grading R (σ := σ) 1 :=
  MvPolynomial.isWeightedHomogeneous_X R (fun _ : σ => (1 : ℕ)) j

/-- Dehomogenisation `R[x_σ] → R[y_k : k ≠ j]`: `x_j ↦ 1`, `x_k ↦ y_k` (`k ≠ j`). -/
def dehomogenize : MvPolynomial σ R →ₐ[R] MvPolynomial {k : σ // k ≠ j} R :=
  MvPolynomial.aeval fun k => if h : k = j then 1 else MvPolynomial.X ⟨k, h⟩

@[simp] lemma dehomogenize_X_self : dehomogenize R j (MvPolynomial.X j) = 1 := by
  simp [dehomogenize]

lemma dehomogenize_X_of_ne {k : σ} (h : k ≠ j) :
    dehomogenize R j (MvPolynomial.X k) = MvPolynomial.X ⟨k, h⟩ := by
  simp [dehomogenize, h]

@[simp] lemma dehomogenize_C (c : R) :
    dehomogenize R j (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [dehomogenize, MvPolynomial.algebraMap_eq]

/-- Forward map `(R[x]_{x_j})_0 → R[y]`: dehomogenisation, through `R[x][1/x_j]` (`x_j` goes to the
unit `1`). -/
def chartToPoly :
    HomogeneousLocalization.Away (grading R (σ := σ)) (MvPolynomial.X j) →+*
      MvPolynomial {k : σ // k ≠ j} R :=
  (IsLocalization.Away.lift (MvPolynomial.X j : MvPolynomial σ R)
      (g := (dehomogenize R j).toRingHom)
      (by simp)).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X j : MvPolynomial σ R)))

/-- Backward map `R[y] → (R[x]_{x_j})_0`: `y_k ↦ x_k / x_j`, `r ↦ r / 1`. -/
def polyToChart :
    MvPolynomial {k : σ // k ≠ j} R →+*
      HomogeneousLocalization.Away (grading R (σ := σ)) (MvPolynomial.X j) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (grading R (σ := σ) 0) _).comp (algebraMap R (grading R (σ := σ) 0)))
    (fun k => HomogeneousLocalization.Away.mk _ (X_mem R j) 1 (MvPolynomial.X k.1)
      (by simpa using MvPolynomial.isWeightedHomogeneous_X R (fun _ : σ => (1 : ℕ)) k.1))

/-- `chartToPoly` on the fraction `a / x_j^n` is the dehomogenisation `a(x_j := 1)`. -/
lemma chartToPoly_mk (n : ℕ) (a : MvPolynomial σ R) (ha : a ∈ grading R (σ := σ) (n • 1)) :
    chartToPoly R j (HomogeneousLocalization.Away.mk _ (X_mem R j) n a ha) =
      dehomogenize R j a := by
  unfold chartToPoly IsLocalization.Away.lift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  simp

omit [DecidableEq σ] in
lemma mk_X_pow_zero (x : MvPolynomial σ R)
    (h : MvPolynomial.X j ^ 0 ∈ Submonoid.powers (MvPolynomial.X j : MvPolynomial σ R)) :
    Localization.mk x ⟨MvPolynomial.X j ^ 0, h⟩ =
      algebraMap _ (Localization.Away (MvPolynomial.X j : MvPolynomial σ R)) x := by
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1

omit [DecidableEq σ] in
lemma mk_X_pow_one (x : MvPolynomial σ R)
    (h : MvPolynomial.X j ^ 1 ∈ Submonoid.powers (MvPolynomial.X j : MvPolynomial σ R)) :
    Localization.mk x ⟨MvPolynomial.X j ^ 1, h⟩ =
      Localization.mk x ⟨MvPolynomial.X j, Submonoid.mem_powers _⟩ := by
  congr 1
  exact Subtype.ext (pow_one _)

lemma polyToChart_X (k : {k : σ // k ≠ j}) :
    polyToChart R j (MvPolynomial.X k) =
      HomogeneousLocalization.Away.mk _ (X_mem R j) 1 (MvPolynomial.X k.1)
        (by simpa using MvPolynomial.isWeightedHomogeneous_X R (fun _ : σ => (1 : ℕ)) k.1) :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma polyToChart_C (c : R) :
    polyToChart R j (MvPolynomial.C c) =
      algebraMap (grading R (σ := σ) 0) _ (algebraMap R (grading R (σ := σ) 0) c) :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- A degree-zero element `z` is the fraction `z / x_j^0`. -/
lemma algebraMap_zero_eq_mk (z : grading R (σ := σ) 0) :
    algebraMap (grading R (σ := σ) 0)
        (HomogeneousLocalization.Away (grading R (σ := σ)) (MvPolynomial.X j)) z =
      HomogeneousLocalization.Away.mk _ (X_mem R j) 0 z.1 (by simp) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, mk_X_pow_zero, ← Localization.mk_one_eq_algebraMap]
  rfl

lemma chartToPoly_comp_polyToChart :
    (chartToPoly R j).comp (polyToChart R j) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_C, algebraMap_zero_eq_mk, chartToPoly_mk]
    simp [MvPolynomial.algebraMap_eq]
  · intro k
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_X, chartToPoly_mk,
      dehomogenize_X_of_ne R j k.2]

/-- Auxiliary: the `R`-algebra map `R[x] → R[x][1/x_j]`, `x_k ↦ x_k / x_j` for every `k`
(including `x_j ↦ 1`). -/
def awayScale :
    MvPolynomial σ R →ₐ[R] Localization.Away (MvPolynomial.X j : MvPolynomial σ R) :=
  MvPolynomial.aeval fun k =>
    Localization.mk (MvPolynomial.X k) ⟨MvPolynomial.X j, Submonoid.mem_powers _⟩

lemma val_polyToChart_dehomogenize (p : MvPolynomial σ R) :
    (polyToChart R j (dehomogenize R j p)).val = awayScale R j p := by
  have h : (algebraMap _ (Localization.Away (MvPolynomial.X j : MvPolynomial σ R))).comp
      ((polyToChart R j).comp (dehomogenize R j).toRingHom) = (awayScale R j).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehomogenize_C,
        polyToChart_C, HomogeneousLocalization.algebraMap_apply, algebraMap_zero_eq_mk,
        HomogeneousLocalization.Away.val_mk, awayScale, MvPolynomial.aeval_C, mk_X_pow_zero]
      simp [MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
          (Localization.Away (MvPolynomial.X j : MvPolynomial σ R))]
    · intro k
      by_cases hk : k = j
      · subst hk
        simp [awayScale]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          dehomogenize_X_of_ne R j hk, polyToChart_X, HomogeneousLocalization.algebraMap_apply,
          HomogeneousLocalization.Away.val_mk, awayScale, MvPolynomial.aeval_X, mk_X_pow_one]
  exact RingHom.congr_fun h p

lemma awayScale_monomial (α : σ →₀ ℕ) (c : R) :
    awayScale R j (MvPolynomial.monomial α c) =
      Localization.mk (MvPolynomial.monomial α c)
        ⟨MvPolynomial.X j ^ (Finsupp.weight (fun _ : σ => (1 : ℕ)) α),
          Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  induction α using Finsupp.induction with
  | zero =>
    simp only [map_zero]
    rw [mk_X_pow_zero]
    simp [awayScale, IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
        (Localization.Away (MvPolynomial.X j : MvPolynomial σ R)),
      MvPolynomial.algebraMap_eq]
  | single_add a b f _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, ih]
    simp only [awayScale, MvPolynomial.aeval_X]
    rw [Localization.mk_pow, Localization.mk_mul]
    congr 1
    exact Subtype.ext (by simp [pow_add, Finsupp.weight_single])

lemma awayScale_of_isWeightedHomogeneous {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : σ => (1 : ℕ)) n) :
    awayScale R j p =
      Localization.mk p ⟨MvPolynomial.X j ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : Finsupp.weight (fun _ : σ => (1 : ℕ)) α = n := hp (MvPolynomial.mem_support_iff.mp hα)
  rw [awayScale_monomial, hd]

lemma polyToChart_comp_chartToPoly :
    (polyToChart R j).comp (chartToPoly R j) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R j) x
  rw [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_polyToChart_dehomogenize, HomogeneousLocalization.Away.val_mk,
    awayScale_of_isWeightedHomogeneous R j (n := n)
      ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (by simpa using ha))]

/-- **The standard chart of `Proj R[x_σ]` is an affine space**: the coordinate ring
`(R[x_σ]_{x_j})_0 ≅ R[y_k : k ≠ j]` (`y_k ↦ x_k / x_j`). -/
def chartRingEquiv :
    HomogeneousLocalization.Away (grading R (σ := σ)) (MvPolynomial.X j) ≃+*
      MvPolynomial {k : σ // k ≠ j} R :=
  RingEquiv.ofRingHom (chartToPoly R j) (polyToChart R j)
    (chartToPoly_comp_polyToChart R j) (polyToChart_comp_chartToPoly R j)

/-- Compatibility with the base: `R → (R[x]_0) → (R[x]_{x_j})_0 → R[y]` is the constant map `C`. -/
lemma chartRingEquiv_comp_fromZeroRingHom_comp_algebraMap :
    (chartRingEquiv R j).toRingHom.comp
      ((HomogeneousLocalization.fromZeroRingHom (grading R (σ := σ))
        (Submonoid.powers (MvPolynomial.X j : MvPolynomial σ R))).comp
          (algebraMap R (grading R (σ := σ) 0))) =
      (MvPolynomial.C : R →+* MvPolynomial {k : σ // k ≠ j} R) := by
  refine RingHom.ext fun c => ?_
  change chartToPoly R j (algebraMap (grading R (σ := σ) 0) _ (algebraMap R _ c)) = _
  rw [algebraMap_zero_eq_mk, chartToPoly_mk]
  simp [MvPolynomial.algebraMap_eq]

end MvPolynomial.StandardProjChart

end
