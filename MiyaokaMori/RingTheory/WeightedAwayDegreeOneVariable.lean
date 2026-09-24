import MiyaokaMori.Prelude

/-! # The degree-zero localization of a weighted polynomial ring at a variable of weight one

The degree-zero homogeneous localization of a weighted polynomial ring at a variable of weight `1`
is a polynomial ring (dehomogenization): for `w_{i₀} = 1`,
`k[x]^{(w)}_(x_{i₀}) ≅ k[y_j : j ≠ i₀]`, `y_j ↦ x_j/x_{i₀}^{w_j}`. When all weights are `1`, this is
the standard chart `≅ 𝔸^N` of `ℙ^N`. These are the charts of `ℙ(w)` (§2 of the paper), needed for
the degree of the weighted power map and the dimension of projective space.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Components and proof obligations of `weightedAwayDegreeOneEquiv`

The auxiliary maps and the proof obligations of the definition are stated before it as named
declarations. The two `letI`s (the weighted grading and the `k`-algebra structure on the degree-zero
localization) are repeated literally in each declaration and are the same terms as in the
definition. -/

/-- Dehomogenization `k[x] → k[y]`: `x_{i₀} ↦ 1`, `x_j ↦ y_j` (`j ≠ i₀`). -/
noncomputable def weightedAwayDegreeOneEquiv.dehom (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (i₀ : σ) : MvPolynomial σ k →+* MvPolynomial {j // j ≠ i₀} k :=
  (MvPolynomial.aeval (R := k) fun j => if h : j = i₀ then 1 else MvPolynomial.X ⟨j, h⟩).toRingHom

/-- The dehomogenization sends `x_{i₀}` to `1`, which is in particular a unit. -/
theorem weightedAwayDegreeOneEquiv.isUnit_dehom_X (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (i₀ : σ) :
    IsUnit (weightedAwayDegreeOneEquiv.dehom k i₀ (MvPolynomial.X i₀)) := by
  simp [weightedAwayDegreeOneEquiv.dehom]

/-- When `w_{i₀} = 1`, `x_{i₀}` is homogeneous of weight `1`. -/
theorem weightedAwayDegreeOneEquiv.X_mem (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) :
    (MvPolynomial.X i₀ : MvPolynomial σ k) ∈ MvPolynomial.weightedHomogeneousSubmodule k w 1 := by
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule, ← h1]
  exact MvPolynomial.isWeightedHomogeneous_X k w i₀

/-- The forward ring map `F`: `a / x_{i₀}^n ∈ k[x]_(x_{i₀}) ⊆ k[x][x_{i₀}⁻¹] ↦ g(a)`. -/
noncomputable def weightedAwayDegreeOneEquiv.forward (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀) →+* MvPolynomial {j // j ≠ i₀} k :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  (Localization.awayLift (weightedAwayDegreeOneEquiv.dehom k i₀) (MvPolynomial.X i₀)
      (weightedAwayDegreeOneEquiv.isUnit_dehom_X k i₀)).comp
    (algebraMap (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i₀)) (Localization.Away (MvPolynomial.X i₀)))


/-! ### Auxiliary lemmas

The proof pattern follows the standard graded version `MvPolynomial.homogeneousAwayXRingEquiv`
(namespace `MvPolynomial.HomogeneousAwayX`): the variable `x_{i₀}` of weight `1` plays the role of the
dehomogenizing variable, and the denominators of the inverse map become `x_{i₀}^{w_j}`.
The two `letI` instances of the signature (the weighted grading and the `k`-algebra structure on the
degree-zero localization) are registered below as local instances via `attribute [local instance]`,
so that the auxiliary lemmas can use `rw`; they are literally the same terms as the `letI`s in the
signature (`instAlgebraK` unfolds by δ), so the three obligations are closed by `exact`. They are
**not** global instances (they are in force only in this file). -/

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The `letI : Algebra k (HomogeneousLocalization.Away …)` of the signature, as a named definition so
that it can serve as a local instance. -/
noncomputable abbrev weightedAwayDegreeOneEquiv.instAlgebraK (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) :
    Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i₀)) :=
  ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
      (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀))).comp
    (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra

attribute [local instance] weightedAwayDegreeOneEquiv.instAlgebraK

@[simp] theorem weightedAwayDegreeOneEquiv.dehom_X_self (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (i₀ : σ) :
    weightedAwayDegreeOneEquiv.dehom k i₀ (MvPolynomial.X i₀) = 1 := by
  simp [weightedAwayDegreeOneEquiv.dehom]

theorem weightedAwayDegreeOneEquiv.dehom_X_of_ne (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (i₀ : σ) {j : σ} (h : j ≠ i₀) :
    weightedAwayDegreeOneEquiv.dehom k i₀ (MvPolynomial.X j) = MvPolynomial.X ⟨j, h⟩ := by
  simp [weightedAwayDegreeOneEquiv.dehom, h]

@[simp] theorem weightedAwayDegreeOneEquiv.dehom_C (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (i₀ : σ) (c : k) :
    weightedAwayDegreeOneEquiv.dehom k i₀ (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [weightedAwayDegreeOneEquiv.dehom, MvPolynomial.algebraMap_eq]

/-- The `val` of the image of a degree-zero element `z` under `fromZeroRingHom` is `z / 1`. -/
theorem weightedAwayDegreeOneEquiv.val_fromZero (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (w : σ → ℕ) (i₀ : σ)
    (z : MvPolynomial.weightedHomogeneousSubmodule k w 0) :
    (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.weightedHomogeneousSubmodule k w)
        (Submonoid.powers (MvPolynomial.X i₀)) z).val =
      algebraMap (MvPolynomial σ k) (Localization.Away (MvPolynomial.X i₀ : MvPolynomial σ k)) z.1 := by
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

/-- `F` on a degree-zero element `z / 1` is `g z` (`w i₀ = 1` is not needed). -/
theorem weightedAwayDegreeOneEquiv.forward_fromZero (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ)
    (z : MvPolynomial.weightedHomogeneousSubmodule k w 0) :
    weightedAwayDegreeOneEquiv.forward k w i₀
        (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.weightedHomogeneousSubmodule k w)
          (Submonoid.powers (MvPolynomial.X i₀)) z) =
      weightedAwayDegreeOneEquiv.dehom k i₀ z.1 := by
  unfold weightedAwayDegreeOneEquiv.forward
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    weightedAwayDegreeOneEquiv.val_fromZero]
  unfold Localization.awayLift
  rw [IsLocalization.Away.lift_eq]

/-- `F` on the fraction `a / x_{i₀}^n` is the dehomogenization `g a`. -/
theorem weightedAwayDegreeOneEquiv.forward_mk (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) (n : ℕ)
    (a : MvPolynomial σ k) (ha : a ∈ MvPolynomial.weightedHomogeneousSubmodule k w (n • 1)) :
    weightedAwayDegreeOneEquiv.forward k w i₀
        (HomogeneousLocalization.Away.mk _ (weightedAwayDegreeOneEquiv.X_mem k w i₀ h1) n a ha) =
      weightedAwayDegreeOneEquiv.dehom k i₀ a := by
  unfold weightedAwayDegreeOneEquiv.forward Localization.awayLift IsLocalization.Away.lift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  simp

/-- `F` is a `k`-algebra map (the `commutes'` field of `AlgHom`):
`F ∘ (k → k[x]_0 → degree-zero localization) = (k → k[y])`. This is the standard dehomogenization
(the weighted version of Hartshorne II.2, Prop. 2.5).

Proof: by the `letI` in the signature, `algebraMap k HL c` equals
`algebraMap (𝒜 0) HL (algebraMap k (𝒜 0) c)`, the image of the degree-zero homogeneous element `c`
(a constant polynomial) under `HomogeneousLocalization.fromZeroRingHom`, i.e. the fraction
`c / x_{i₀}^0 = c / 1` (`val_fromZero`, via `Localization.mk_one_eq_algebraMap`). `F` sends it through
`algebraMap HL (Localization.Away (X i₀))` to `c / 1` and then through `Localization.awayLift g` to
`g c` (`IsLocalization.Away.lift_eq`); as `g = dehom` is an `aeval`, the image of `C c` is `C c`, i.e.
`algebraMap k (k[y]) c` (`SetLike.GradeZero.coe_algebraMap`); see `forward_fromZero`. -/
theorem weightedAwayDegreeOneEquiv.forward_commutes (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) :=
      ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
          (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
            (MvPolynomial.X i₀))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
    ∀ r : k, weightedAwayDegreeOneEquiv.forward k w i₀
        (algebraMap k (HomogeneousLocalization.Away
          (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀)) r) =
      algebraMap k (MvPolynomial {j // j ≠ i₀} k) r := by
  intro r
  refine (weightedAwayDegreeOneEquiv.forward_fromZero k w i₀
    (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0) r)).trans ?_
  simp [weightedAwayDegreeOneEquiv.dehom, MvPolynomial.algebraMap_eq]

/-- The forward `k`-algebra map (`F` together with `commutes'`). -/
noncomputable def weightedAwayDegreeOneEquiv.forwardAlg (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) :=
      ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
          (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
            (MvPolynomial.X i₀))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
    HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀) →ₐ[k] MvPolynomial {j // j ≠ i₀} k :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i₀)) :=
    ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
        (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
          (MvPolynomial.X i₀))).comp
      (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
  { weightedAwayDegreeOneEquiv.forward k w i₀ with
    commutes' := weightedAwayDegreeOneEquiv.forward_commutes k w i₀ }

/-- The inverse `k`-algebra map `B`: `y_j ↦ x_j / x_{i₀}^{w_j}` (`x_{i₀}` has weight `1`,
`x_j ∈ 𝒜 (w_j • 1)`). -/
noncomputable def weightedAwayDegreeOneEquiv.backward (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) :=
      ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
          (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
            (MvPolynomial.X i₀))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
    MvPolynomial {j // j ≠ i₀} k →ₐ[k]
      HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀) :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i₀)) :=
    ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
        (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
          (MvPolynomial.X i₀))).comp
      (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
  MvPolynomial.aeval fun j => HomogeneousLocalization.Away.mk
    (MvPolynomial.weightedHomogeneousSubmodule k w)
    (weightedAwayDegreeOneEquiv.X_mem k w i₀ h1) (w j.1) (MvPolynomial.X j.1)
    (by rw [smul_eq_mul, mul_one, MvPolynomial.mem_weightedHomogeneousSubmodule]
        exact MvPolynomial.isWeightedHomogeneous_X k w j.1)


theorem weightedAwayDegreeOneEquiv.forwardAlg_apply (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ)
    (x : HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i₀)) :
    weightedAwayDegreeOneEquiv.forwardAlg k w i₀ x = weightedAwayDegreeOneEquiv.forward k w i₀ x :=
  rfl

/-- `x_j ∈ 𝒜 (w_j • 1)` (the membership proof used in the definition of `backward`). -/
theorem weightedAwayDegreeOneEquiv.X_mem_smul (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (j : σ) :
    (MvPolynomial.X j : MvPolynomial σ k) ∈
      MvPolynomial.weightedHomogeneousSubmodule k w (w j • 1) := by
  rw [smul_eq_mul, mul_one, MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact MvPolynomial.isWeightedHomogeneous_X k w j

theorem weightedAwayDegreeOneEquiv.backward_X (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) (j : {j // j ≠ i₀}) :
    weightedAwayDegreeOneEquiv.backward k w i₀ h1 (MvPolynomial.X j) =
      HomogeneousLocalization.Away.mk _ (weightedAwayDegreeOneEquiv.X_mem k w i₀ h1) (w j.1)
        (MvPolynomial.X j.1) (weightedAwayDegreeOneEquiv.X_mem_smul k w j.1) :=
  MvPolynomial.aeval_X _ _

theorem weightedAwayDegreeOneEquiv.backward_C (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) (c : k) :
    weightedAwayDegreeOneEquiv.backward k w i₀ h1 (MvPolynomial.C c) =
      HomogeneousLocalization.fromZeroRingHom (MvPolynomial.weightedHomogeneousSubmodule k w)
        (Submonoid.powers (MvPolynomial.X i₀))
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0) c) :=
  MvPolynomial.aeval_C _ _

/-- Auxiliary `k`-algebra map `k[x] → k[x][x_{i₀}⁻¹]`, `x_j ↦ x_j / x_{i₀}^{w_j}` (for all `j`; when
`w_{i₀} = 1`, `x_{i₀} ↦ 1`). -/
noncomputable def weightedAwayDegreeOneEquiv.awayScale (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) :
    MvPolynomial σ k →ₐ[k] Localization.Away (MvPolynomial.X i₀ : MvPolynomial σ k) :=
  MvPolynomial.aeval fun j => Localization.mk (MvPolynomial.X j)
    ⟨MvPolynomial.X i₀ ^ w j, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩

/-- The `val` of `B(g p)` is `awayScale p`. -/
theorem weightedAwayDegreeOneEquiv.val_backward_dehom (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) (p : MvPolynomial σ k) :
    (weightedAwayDegreeOneEquiv.backward k w i₀ h1 (weightedAwayDegreeOneEquiv.dehom k i₀ p)).val =
      weightedAwayDegreeOneEquiv.awayScale k w i₀ p := by
  have h : (algebraMap _ (Localization.Away (MvPolynomial.X i₀ : MvPolynomial σ k))).comp
      ((weightedAwayDegreeOneEquiv.backward k w i₀ h1).toRingHom.comp
        (weightedAwayDegreeOneEquiv.dehom k i₀)) =
      (weightedAwayDegreeOneEquiv.awayScale k w i₀).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        weightedAwayDegreeOneEquiv.dehom_C, weightedAwayDegreeOneEquiv.backward_C,
        HomogeneousLocalization.algebraMap_apply, weightedAwayDegreeOneEquiv.val_fromZero,
        weightedAwayDegreeOneEquiv.awayScale, MvPolynomial.aeval_C]
      simp [MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply k (MvPolynomial σ k)
          (Localization.Away (MvPolynomial.X i₀ : MvPolynomial σ k))]
    · intro j
      by_cases hj : j = i₀
      · subst hj
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          weightedAwayDegreeOneEquiv.dehom_X_self, map_one,
          weightedAwayDegreeOneEquiv.awayScale, MvPolynomial.aeval_X]
        have hden : (⟨MvPolynomial.X j ^ w j, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ :
            Submonoid.powers (MvPolynomial.X j : MvPolynomial σ k)) =
            ⟨MvPolynomial.X j, Submonoid.mem_powers _⟩ :=
          Subtype.ext (show MvPolynomial.X j ^ w j = MvPolynomial.X j by rw [h1, pow_one])
        rw [hden]
        exact (Localization.mk_self (⟨MvPolynomial.X j, Submonoid.mem_powers _⟩ :
          Submonoid.powers (MvPolynomial.X j : MvPolynomial σ k))).symm
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          weightedAwayDegreeOneEquiv.dehom_X_of_ne k i₀ hj, weightedAwayDegreeOneEquiv.backward_X,
          HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
          weightedAwayDegreeOneEquiv.awayScale, MvPolynomial.aeval_X]
  exact RingHom.congr_fun h p

theorem weightedAwayDegreeOneEquiv.mk_X_pow_zero (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (i₀ : σ) (x : MvPolynomial σ k)
    (h : MvPolynomial.X i₀ ^ 0 ∈ Submonoid.powers (MvPolynomial.X i₀ : MvPolynomial σ k)) :
    Localization.mk x ⟨MvPolynomial.X i₀ ^ 0, h⟩ =
      algebraMap _ (Localization.Away (MvPolynomial.X i₀ : MvPolynomial σ k)) x := by
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1

/-- `awayScale` on the monomial `x^α` is `x^α / x_{i₀}^{weight w α}` (`w_{i₀} = 1` is not needed). -/
theorem weightedAwayDegreeOneEquiv.awayScale_monomial (k : Type u) [Field k] {σ : Type u}
    [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (α : σ →₀ ℕ) (c : k) :
    weightedAwayDegreeOneEquiv.awayScale k w i₀ (MvPolynomial.monomial α c) =
      Localization.mk (MvPolynomial.monomial α c)
        ⟨MvPolynomial.X i₀ ^ Finsupp.weight w α, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  induction α using Finsupp.induction with
  | zero =>
    simp only [map_zero]
    rw [weightedAwayDegreeOneEquiv.mk_X_pow_zero]
    simp [weightedAwayDegreeOneEquiv.awayScale, IsScalarTower.algebraMap_apply k (MvPolynomial σ k)
        (Localization.Away (MvPolynomial.X i₀ : MvPolynomial σ k)),
      MvPolynomial.algebraMap_eq]
  | single_add a b f _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, ih]
    simp only [weightedAwayDegreeOneEquiv.awayScale, MvPolynomial.aeval_X]
    rw [Localization.mk_pow, Localization.mk_mul]
    congr 1
    exact Subtype.ext (by
      show (MvPolynomial.X i₀ ^ w a) ^ b * MvPolynomial.X i₀ ^ Finsupp.weight w f =
        MvPolynomial.X i₀ ^ Finsupp.weight w (Finsupp.single a b + f)
      rw [map_add, Finsupp.weight_single, smul_eq_mul, pow_add, mul_comm b, pow_mul])

/-- `awayScale` on a weighted homogeneous polynomial `p` of weight `n` is `p / x_{i₀}^n`. -/
theorem weightedAwayDegreeOneEquiv.awayScale_of_isWeightedHomogeneous (k : Type u) [Field k]
    {σ : Type u} [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) :
    weightedAwayDegreeOneEquiv.awayScale k w i₀ p =
      Localization.mk p ⟨MvPolynomial.X i₀ ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩ := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : Finsupp.weight w α = n := hp (MvPolynomial.mem_support_iff.mp hα)
  subst hd
  exact weightedAwayDegreeOneEquiv.awayScale_monomial k w i₀ α _

/-- `F ∘ B = id`, written with the local instances of this file (δ/ζ-equal to the statement of
`forward_comp_backward`). -/
theorem weightedAwayDegreeOneEquiv.forward_comp_backward' (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) :
    (weightedAwayDegreeOneEquiv.forwardAlg k w i₀).comp
        (weightedAwayDegreeOneEquiv.backward k w i₀ h1) =
      AlgHom.id k (MvPolynomial {j // j ≠ i₀} k) := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [AlgHom.comp_apply, AlgHom.id_apply, weightedAwayDegreeOneEquiv.backward_X,
    weightedAwayDegreeOneEquiv.forwardAlg_apply, weightedAwayDegreeOneEquiv.forward_mk k w i₀ h1,
    weightedAwayDegreeOneEquiv.dehom_X_of_ne k i₀ j.2]

/-- `B ∘ F = id`, written with the local instances of this file (δ/ζ-equal to the statement of
`backward_comp_forward`). -/
theorem weightedAwayDegreeOneEquiv.backward_comp_forward' (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) :
    (weightedAwayDegreeOneEquiv.backward k w i₀ h1).comp
        (weightedAwayDegreeOneEquiv.forwardAlg k w i₀) =
      AlgHom.id k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (weightedAwayDegreeOneEquiv.X_mem k w i₀ h1) x
  rw [AlgHom.comp_apply, AlgHom.id_apply, weightedAwayDegreeOneEquiv.forwardAlg_apply,
    weightedAwayDegreeOneEquiv.forward_mk k w i₀ h1]
  apply HomogeneousLocalization.val_injective
  rw [weightedAwayDegreeOneEquiv.val_backward_dehom, HomogeneousLocalization.Away.val_mk,
    weightedAwayDegreeOneEquiv.awayScale_of_isWeightedHomogeneous k w i₀ (n := n)
      ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (by simpa using ha))]

/-- `F ∘ B = id` (on `k[y]`): `y_j ↦ x_j / x_{i₀}^{w_j} ↦ g(x_j)/g(x_{i₀})^{w_j} = y_j / 1 = y_j`.

Proof: both sides are `k`-algebra maps `k[y] → k[y]`, so by `MvPolynomial.algHom_ext` it suffices to
check on the generators `y_j`. `B y_j = x_j / x_{i₀}^{w_j}` (`HomogeneousLocalization.Away.mk`), and
`F` sends this to `g(x_j) / g(x_{i₀})^{w_j}` (`forward_mk`); since `g(x_{i₀}) = 1` (`dehom_X_self`) and
`g(x_j) = y_j` for `j ≠ i₀` (`dehom_X_of_ne`), the image is `y_j`.
The statement is the δ/ζ-restatement of `forward_comp_backward'` (written with the local instances of
this file). -/
theorem weightedAwayDegreeOneEquiv.forward_comp_backward (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) :=
      ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
          (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
            (MvPolynomial.X i₀))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
    (weightedAwayDegreeOneEquiv.forwardAlg k w i₀).comp
        (weightedAwayDegreeOneEquiv.backward k w i₀ h1) =
      AlgHom.id k (MvPolynomial {j // j ≠ i₀} k) :=
  weightedAwayDegreeOneEquiv.forward_comp_backward' k w i₀ h1

/-- `B ∘ F = id` (on the degree-zero localization).

Proof sketch: elements of the degree-zero localization are of the form `a / x_{i₀}^n` with `a`
weighted homogeneous of weight `n` (`HomogeneousLocalization.Away.mk_surjective`; `w_{i₀} = 1` makes
the weight of the denominator exactly `n`). Following the route of the standard graded version
`MvPolynomial.HomogeneousAwayX.polyToChart_comp_chartToPoly`: the auxiliary `k`-algebra map
`awayScale : k[x] → k[x][x_{i₀}⁻¹]`, `x_j ↦ x_j / x_{i₀}^{w_j}` (for all `j`), satisfies
`(B (g p)).val = awayScale p` (`val_backward_dehom`, checked on generators; at `j = i₀` use
`w_{i₀} = 1` and `Localization.mk_self`); `awayScale (x^e) = x^e / x_{i₀}^{weight w e}`
(`awayScale_monomial`, by `Finsupp.induction`, `Localization.mk_pow/mk_mul`, `Finsupp.weight_single`);
and for `p` weighted homogeneous of weight `n`, `awayScale p = p / x_{i₀}^n`
(`awayScale_of_isWeightedHomogeneous`, `as_sum` + `Localization.mk_sum`). Hence `B (F (a / x_{i₀}^n))`
has `val` equal to `a / x_{i₀}^n`.

Edge cases: for `n = 0`, `a` is a constant and both sides are images of `algebraMap k`
(`forward_commutes`); for `σ = {i₀}`, `k[y]` is the polynomial ring in no variables, i.e. `k`, and both
sides are the identity.

The statement is the δ/ζ-restatement of `backward_comp_forward'` (written with the local instances of
this file). -/
theorem weightedAwayDegreeOneEquiv.backward_comp_forward (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) :=
      ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
          (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
            (MvPolynomial.X i₀))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
    (weightedAwayDegreeOneEquiv.backward k w i₀ h1).comp
        (weightedAwayDegreeOneEquiv.forwardAlg k w i₀) =
      AlgHom.id k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) :=
  weightedAwayDegreeOneEquiv.backward_comp_forward' k w i₀ h1

noncomputable def weightedAwayDegreeOneEquiv (k : Type u) [Field k] {σ : Type u} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (i₀ : σ) (h1 : w i₀ = 1) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    /- `k`-algebra structure: `k → k[x]_0` (degree-zero part, `SetLike.GradeZero.instAlgebra`) → degree-zero
       localization (`fromZeroRingHom`) -/
    letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i₀)) :=
      ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
          (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
            (MvPolynomial.X i₀))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
    HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i₀) ≃ₐ[k]
      MvPolynomial {j // j ≠ i₀} k :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI : Algebra k (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i₀)) :=
    ((algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
        (HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
          (MvPolynomial.X i₀))).comp
      (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))).toAlgebra
  AlgEquiv.ofAlgHom (weightedAwayDegreeOneEquiv.forwardAlg k w i₀)
    (weightedAwayDegreeOneEquiv.backward k w i₀ h1)
    (weightedAwayDegreeOneEquiv.forward_comp_backward k w i₀ h1)
    (weightedAwayDegreeOneEquiv.backward_comp_forward k w i₀ h1)

end
