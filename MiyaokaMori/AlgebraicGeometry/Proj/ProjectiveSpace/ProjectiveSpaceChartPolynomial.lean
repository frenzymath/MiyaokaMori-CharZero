import MiyaokaMori.Prelude

/-! # The coordinate ring of a standard chart of projective space

The coordinate ring of the standard affine chart `D₊(x_i)` of `P^N_k`: the degree-zero homogeneous
localization `k[x₀..x_N]_(x_i)` is isomorphic to the polynomial ring `k[x_j/x_i : j ≠ i]` in `N`
variables (Hartshorne II.2.5, Stacks 01M6).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `x_i` is homogeneous of degree one, written as a member of `homogeneousSubmodule` so that it
matches `Away.mk`/`Away.val_mk`. -/
lemma ProjectiveSpace.X_mem (N : ℕ) (k : Type u) [Field k] (i : Fin (N + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 1 :=
  MvPolynomial.isHomogeneous_X k i

/-- Dehomogenization `k[x₀..x_N] → k[X_j : j ≠ i]`: `x_i ↦ 1`, `x_j ↦ X_j` for `j ≠ i`. -/

noncomputable def ProjectiveSpace.dehomogenize (N : ℕ) (k : Type u) [Field k] (i : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) k →ₐ[k] MvPolynomial {j : Fin (N + 1) // j ≠ i} k :=
  MvPolynomial.aeval fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

/-- Forward map: dehomogenization `x_i ↦ 1` on `k[x]_(x_i) ⊆ k[x][1/x_i]` (`x_i` is sent to the unit `1`,
so the universal property of the localization applies). -/

noncomputable def ProjectiveSpace.chartToPoly (N : ℕ) (k : Type u) [Field k] (i : Fin (N + 1)) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)
      →+* MvPolynomial {j : Fin (N + 1) // j ≠ i} k :=
  (IsLocalization.Away.lift (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)
      (g := (ProjectiveSpace.dehomogenize N k i).toRingHom)
      (by simp [ProjectiveSpace.dehomogenize])).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)))

/-- Inverse map: `X_j ↦ x_j / x_i` (a degree-zero homogeneous fraction), coefficients `c ↦ c/1`. -/

noncomputable def ProjectiveSpace.polyToChart (N : ℕ) (k : Type u) [Field k] (i : Fin (N + 1)) :
    MvPolynomial {j : Fin (N + 1) // j ≠ i} k →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) _).comp
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))
    (fun j => HomogeneousLocalization.Away.mk _ (ProjectiveSpace.X_mem N k i) 1 (MvPolynomial.X j.1)
      (by simpa using MvPolynomial.isHomogeneous_X k j.1))

namespace ProjectiveSpace

variable (N : ℕ) (k : Type u) [Field k] (i : Fin (N + 1))

@[simp] lemma dehomogenize_X_self : dehomogenize N k i (MvPolynomial.X i) = 1 := by
  simp [dehomogenize]

lemma dehomogenize_X_of_ne {j : Fin (N + 1)} (h : j ≠ i) :
    dehomogenize N k i (MvPolynomial.X j) = MvPolynomial.X ⟨j, h⟩ := by
  simp [dehomogenize, h]

@[simp] lemma dehomogenize_C (c : k) :
    dehomogenize N k i (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [dehomogenize, MvPolynomial.algebraMap_eq]

/-- The value of `chartToPoly` on the fraction `a / x_i^n` is the dehomogenization `a(x_i := 1)`. -/
lemma chartToPoly_mk (n : ℕ) (a : MvPolynomial (Fin (N + 1)) k)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k (n • 1)) :
    chartToPoly N k i
        (HomogeneousLocalization.Away.mk _ (ProjectiveSpace.X_mem N k i) n a ha) =
      dehomogenize N k i a := by
  unfold chartToPoly IsLocalization.Away.lift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  simp

lemma mk_X_pow_zero (x : MvPolynomial (Fin (N + 1)) k)
    (h : MvPolynomial.X i ^ 0 ∈ Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) :
    Localization.mk x ⟨MvPolynomial.X i ^ 0, h⟩ =
      algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) x := by
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1

lemma mk_X_pow_one (x : MvPolynomial (Fin (N + 1)) k)
    (h : MvPolynomial.X i ^ 1 ∈ Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) :
    Localization.mk x ⟨MvPolynomial.X i ^ 1, h⟩ =
      Localization.mk x ⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ := by
  congr 1
  exact Subtype.ext (pow_one _)

lemma polyToChart_X (j : {j : Fin (N + 1) // j ≠ i}) :
    polyToChart N k i (MvPolynomial.X j) =
      HomogeneousLocalization.Away.mk _ (ProjectiveSpace.X_mem N k i) 1 (MvPolynomial.X j.1)
        (by simpa using MvPolynomial.isHomogeneous_X k j.1) :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma polyToChart_C (c : k) :
    polyToChart N k i (MvPolynomial.C c) =
      algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) _
        (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) c) :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- A degree-zero element `z` is the fraction `z / x_i^0` in `k[x]_(x_i)`. -/
lemma algebraMap_zero_eq_mk (z : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) :
    algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
          (MvPolynomial.X i)) z =
      HomogeneousLocalization.Away.mk _ (ProjectiveSpace.X_mem N k i) 0 z.1
        (by simpa using z.2) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, mk_X_pow_zero, ← Localization.mk_one_eq_algebraMap]
  rfl

lemma chartToPoly_comp_polyToChart :
    (chartToPoly N k i).comp (polyToChart N k i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_C, algebraMap_zero_eq_mk, chartToPoly_mk]
    simp [MvPolynomial.algebraMap_eq]
  · intro j
    rw [RingHom.comp_apply, RingHom.id_apply, polyToChart_X, chartToPoly_mk,
      dehomogenize_X_of_ne N k i j.2]

/-- Auxiliary `k`-algebra homomorphism `k[x] → k[x][1/x_i]`, `x_j ↦ x_j / x_i` for all `j`
(including `x_i ↦ 1`). -/
noncomputable def awayScale :
    MvPolynomial (Fin (N + 1)) k →ₐ[k]
      Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) :=
  MvPolynomial.aeval fun j =>
    Localization.mk (MvPolynomial.X j) ⟨MvPolynomial.X i, Submonoid.mem_powers _⟩

lemma val_polyToChart_dehomogenize (p : MvPolynomial (Fin (N + 1)) k) :
    (polyToChart N k i (dehomogenize N k i p)).val = awayScale N k i p := by
  have h : (algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))).comp
      ((polyToChart N k i).comp (dehomogenize N k i).toRingHom) = (awayScale N k i).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehomogenize_C,
        polyToChart_C, HomogeneousLocalization.algebraMap_apply, algebraMap_zero_eq_mk,
        HomogeneousLocalization.Away.val_mk, awayScale, MvPolynomial.aeval_C, mk_X_pow_zero]
      simp [MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (N + 1)) k)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k))]
    · intro j
      by_cases hj : j = i
      · subst hj
        simp [awayScale]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          dehomogenize_X_of_ne N k i hj, polyToChart_X, HomogeneousLocalization.algebraMap_apply,
          HomogeneousLocalization.Away.val_mk, awayScale, MvPolynomial.aeval_X, mk_X_pow_one]
  exact RingHom.congr_fun h p

lemma awayScale_monomial (α : Fin (N + 1) →₀ ℕ) (c : k) :
    awayScale N k i (MvPolynomial.monomial α c) =
      Localization.mk (MvPolynomial.monomial α c)
        ⟨MvPolynomial.X i ^ α.degree, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  induction α using Finsupp.induction with
  | zero =>
    simp only [map_zero]
    rw [mk_X_pow_zero]
    simp [awayScale, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin (N + 1)) k)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)),
      MvPolynomial.algebraMap_eq]
  | single_add a b f _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, ih]
    simp only [awayScale, MvPolynomial.aeval_X]
    rw [Localization.mk_pow, Localization.mk_mul]
    congr 1
    exact Subtype.ext (by simp [pow_add])

lemma awayScale_of_isHomogeneous {p : MvPolynomial (Fin (N + 1)) k} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    awayScale N k i p =
      Localization.mk p ⟨MvPolynomial.X i ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : α.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hα)
  subst hd
  exact awayScale_monomial N k i α _

lemma polyToChart_comp_chartToPoly :
    (polyToChart N k i).comp (chartToPoly N k i) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (ProjectiveSpace.X_mem N k i) x
  rw [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_polyToChart_dehomogenize, HomogeneousLocalization.Away.val_mk,
    awayScale_of_isHomogeneous N k i (n := n)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp (by simpa using ha))]

end ProjectiveSpace

/-- The chart coordinate ring isomorphism `k[x]_(x_i) ≅ k[X_j : j ≠ i]`; the two maps are mutually
inverse by `chartToPoly_comp_polyToChart` and `polyToChart_comp_chartToPoly`. -/

noncomputable def ProjectiveSpace.chartRingEquiv (N : ℕ) (k : Type u) [Field k] (i : Fin (N + 1)) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)
      ≃+* MvPolynomial {j : Fin (N + 1) // j ≠ i} k :=
  RingEquiv.ofRingHom (ProjectiveSpace.chartToPoly N k i) (ProjectiveSpace.polyToChart N k i)
    (ProjectiveSpace.chartToPoly_comp_polyToChart N k i)
    (ProjectiveSpace.polyToChart_comp_chartToPoly N k i)

end
