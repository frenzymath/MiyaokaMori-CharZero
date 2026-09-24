import MiyaokaMori.Prelude

/-! # Dehomogenization: the degree-zero localization of a polynomial ring at a variable

Statement (dehomogenisation over an arbitrary commutative ring). Let `R` be a commutative ring, `σ` a type with
decidable equality and `i : σ`. Give `R[x_σ] = MvPolynomial σ R` its standard grading
(`MvPolynomial.homogeneousSubmodule σ R`, `MvPolynomial.gradedAlgebra`). Then the degree-0 homogeneous
localisation at the degree-1 variable `x_i` is the polynomial ring in the remaining variables:
`HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X i) ≃+* MvPolynomial {j // j ≠ i} R`,
`a / x_i^n ↦ a(x_i := 1)` and `y_j ↦ x_j / x_i`.

Proof. Forward map: `a / x_i^n ↦ a(x_i := 1, x_j := y_j)`, obtained from the universal property of the
localisation `R[x][1/x_i]` (`IsLocalization.Away.lift`: `x_i` is sent to the unit `1`) restricted to the degree-0
subring. Backward map: the ring map `R[y] → (R[x]_{x_i})_0` sending `c ↦ c/1`, `y_j ↦ x_j / x_i`
(`HomogeneousLocalization.Away.mk`, `x_j` homogeneous of degree `1 = 1 • 1`). Forward ∘ backward = id: check
on the generators `c` and `y_j` (`MvPolynomial.ringHom_ext`): `c/1 ↦ c`, `x_j/x_i ↦ y_j`. Backward ∘ forward =
id: every element is `a / x_i^n` with `a` homogeneous of degree `n` (`Away.mk_surjective`); the `val` of
backward(forward(a/x_i^n)) is the image of `a` under `x_j ↦ x_j/x_i` (for all `j`, including `x_i ↦ 1`), which on
a monomial of degree `n` is `monomial / x_i^n`, hence on `a` is `a / x_i^n` (`awayScale_of_isHomogeneous`).

This is the field case `ProjectiveSpace.chartRingEquiv` (`ProjectiveSpaceChartPolynomial`,
index type `Fin (N+1)`, coefficients a field) with `Field k` weakened to `CommRing R` and the index type made
arbitrary: the proof there never used the field structure. Names are prefixed `MvPolynomial.HomogeneousAwayX` so they
do not collide with the field-case names.

Edge cases: `σ = {i}`: the right-hand side is `MvPolynomial (Empty-like) R ≅ R`, the left is `(R[x_i]_{x_i})_0 ≅ R`;
`R` the zero ring: both sides are the zero ring. No hypothesis on `R` is needed.

Source: Hartshorne II.2.5 (D_+(x_i) ≅ A^n), Stacks 01NE / 00JP. Used for the local structure of a
relative `Proj` (Krull dimension, smoothness, integrality of the charts).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial.HomogeneousAwayX

variable (R : Type u) [CommRing R] {σ : Type u} [DecidableEq σ] (i : σ)

/-- `x_i` is homogeneous of degree 1 (as a member of `homogeneousSubmodule`, the form `Away.mk` needs). -/
lemma X_mem :
    (MvPolynomial.X i : MvPolynomial σ R) ∈ MvPolynomial.homogeneousSubmodule σ R 1 :=
  MvPolynomial.isHomogeneous_X R i

/-- Dehomogenisation `R[x_σ] → R[y_j : j ≠ i]`: `x_i ↦ 1`, `x_j ↦ y_j` (`j ≠ i`). -/
def dehomogenize : MvPolynomial σ R →ₐ[R] MvPolynomial {j : σ // j ≠ i} R :=
  MvPolynomial.aeval fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

/-- Forward map `(R[x]_{x_i})_0 → R[y]`: dehomogenisation with `x_i ↦ 1`, through the localisation `R[x][1/x_i]`. -/
def chartToPoly :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i)
      →+* MvPolynomial {j : σ // j ≠ i} R :=
  (IsLocalization.Away.lift (MvPolynomial.X i : MvPolynomial σ R)
      (g := (dehomogenize R i).toRingHom)
      (by simp [dehomogenize])).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial σ R)))

/-- Backward map `R[y] → (R[x]_{x_i})_0`: `y_j ↦ x_j / x_i`, `c ↦ c / 1`. -/
def polyToChart :
    MvPolynomial {j : σ // j ≠ i} R →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial.homogeneousSubmodule σ R 0) _).comp
      (algebraMap R (MvPolynomial.homogeneousSubmodule σ R 0)))
    (fun j => HomogeneousLocalization.Away.mk _ (X_mem R i) 1 (MvPolynomial.X j.1)
      (by simpa using MvPolynomial.isHomogeneous_X R j.1))

@[simp] lemma dehomogenize_X_self : dehomogenize R i (MvPolynomial.X i) = 1 := by
  simp [dehomogenize]

lemma dehomogenize_X_of_ne {j : σ} (h : j ≠ i) :
    dehomogenize R i (MvPolynomial.X j) = MvPolynomial.X ⟨j, h⟩ := by
  simp [dehomogenize, h]

@[simp] lemma dehomogenize_C (c : R) :
    dehomogenize R i (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [dehomogenize, MvPolynomial.algebraMap_eq]

/-- `chartToPoly` on the fraction `a / x_i^n` is the dehomogenisation `a(x_i := 1)`. -/
lemma chartToPoly_mk (n : ℕ) (a : MvPolynomial σ R)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule σ R (n • 1)) :
    chartToPoly R i (HomogeneousLocalization.Away.mk _ (X_mem R i) n a ha) =
      dehomogenize R i a := by
  unfold chartToPoly IsLocalization.Away.lift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  simp

lemma mk_X_pow_zero (x : MvPolynomial σ R)
    (h : MvPolynomial.X i ^ 0 ∈ Submonoid.powers (MvPolynomial.X i : MvPolynomial σ R)) :
    Localization.mk x ⟨MvPolynomial.X i ^ 0, h⟩ =
      algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial σ R)) x := by
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1

lemma mk_X_pow_one (x : MvPolynomial σ R)
    (h : MvPolynomial.X i ^ 1 ∈ Submonoid.powers (MvPolynomial.X i : MvPolynomial σ R)) :
    Localization.mk x ⟨MvPolynomial.X i ^ 1, h⟩ =
      Localization.mk x ⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ := by
  congr 1
  exact Subtype.ext (pow_one _)

lemma polyToChart_X (j : {j : σ // j ≠ i}) :
    polyToChart R i (MvPolynomial.X j) =
      HomogeneousLocalization.Away.mk _ (X_mem R i) 1 (MvPolynomial.X j.1)
        (by simpa using MvPolynomial.isHomogeneous_X R j.1) :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma polyToChart_C (c : R) :
    polyToChart R i (MvPolynomial.C c) =
      algebraMap (MvPolynomial.homogeneousSubmodule σ R 0) _
        (algebraMap R (MvPolynomial.homogeneousSubmodule σ R 0) c) :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- A degree-0 element `z` is the fraction `z / x_i^0` in `(R[x]_{x_i})_0`. -/
lemma algebraMap_zero_eq_mk (z : MvPolynomial.homogeneousSubmodule σ R 0) :
    algebraMap (MvPolynomial.homogeneousSubmodule σ R 0)
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i)) z =
      HomogeneousLocalization.Away.mk _ (X_mem R i) 0 z.1 (by simpa using z.2) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, mk_X_pow_zero, ← Localization.mk_one_eq_algebraMap]
  rfl

lemma chartToPoly_comp_polyToChart :
    (chartToPoly R i).comp (polyToChart R i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_C, algebraMap_zero_eq_mk, chartToPoly_mk]
    simp [MvPolynomial.algebraMap_eq]
  · intro j
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_X, chartToPoly_mk,
      dehomogenize_X_of_ne R i j.2]

/-- Auxiliary: the `R`-algebra map `R[x] → R[x][1/x_i]`, `x_j ↦ x_j / x_i` for all `j` (so `x_i ↦ 1`). -/
def awayScale :
    MvPolynomial σ R →ₐ[R] Localization.Away (MvPolynomial.X i : MvPolynomial σ R) :=
  MvPolynomial.aeval fun j =>
    Localization.mk (MvPolynomial.X j) ⟨MvPolynomial.X i, Submonoid.mem_powers _⟩

lemma val_polyToChart_dehomogenize (p : MvPolynomial σ R) :
    (polyToChart R i (dehomogenize R i p)).val = awayScale R i p := by
  have h : (algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial σ R))).comp
      ((polyToChart R i).comp (dehomogenize R i).toRingHom) = (awayScale R i).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehomogenize_C,
        polyToChart_C, HomogeneousLocalization.algebraMap_apply, algebraMap_zero_eq_mk,
        HomogeneousLocalization.Away.val_mk, awayScale, MvPolynomial.aeval_C, mk_X_pow_zero]
      simp [MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial σ R))]
    · intro j
      by_cases hj : j = i
      · subst hj
        simp [awayScale]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          dehomogenize_X_of_ne R i hj, polyToChart_X, HomogeneousLocalization.algebraMap_apply,
          HomogeneousLocalization.Away.val_mk, awayScale, MvPolynomial.aeval_X, mk_X_pow_one]
  exact RingHom.congr_fun h p

lemma awayScale_monomial (α : σ →₀ ℕ) (c : R) :
    awayScale R i (MvPolynomial.monomial α c) =
      Localization.mk (MvPolynomial.monomial α c)
        ⟨MvPolynomial.X i ^ α.degree, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  induction α using Finsupp.induction with
  | zero =>
    simp only [map_zero]
    rw [mk_X_pow_zero]
    simp [awayScale, IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial σ R)),
      MvPolynomial.algebraMap_eq]
  | single_add a b f _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, ih]
    simp only [awayScale, MvPolynomial.aeval_X]
    rw [Localization.mk_pow, Localization.mk_mul]
    congr 1
    exact Subtype.ext (by simp [pow_add])

lemma awayScale_of_isHomogeneous {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    awayScale R i p =
      Localization.mk p ⟨MvPolynomial.X i ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : α.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hα)
  subst hd
  exact awayScale_monomial R i α _

lemma polyToChart_comp_chartToPoly :
    (polyToChart R i).comp (chartToPoly R i) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R i) x
  rw [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_polyToChart_dehomogenize, HomogeneousLocalization.Away.val_mk,
    awayScale_of_isHomogeneous R i (n := n)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp (by simpa using ha))]

end MvPolynomial.HomogeneousAwayX

/-- **Dehomogenisation**: `(R[x_σ]_{x_i})_0 ≃+* R[y_j : j ≠ i]` for any commutative ring `R`
(`a / x_i^n ↦ a(x_i := 1)`, `y_j ↦ x_j / x_i`). -/
def MvPolynomial.homogeneousAwayXRingEquiv (R : Type u) [CommRing R] {σ : Type u} [DecidableEq σ] (i : σ) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i)
      ≃+* MvPolynomial {j : σ // j ≠ i} R :=
  RingEquiv.ofRingHom (MvPolynomial.HomogeneousAwayX.chartToPoly R i)
    (MvPolynomial.HomogeneousAwayX.polyToChart R i)
    (MvPolynomial.HomogeneousAwayX.chartToPoly_comp_polyToChart R i)
    (MvPolynomial.HomogeneousAwayX.polyToChart_comp_chartToPoly R i)

end
