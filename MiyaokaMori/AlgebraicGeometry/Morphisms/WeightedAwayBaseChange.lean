import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.GradedRing.HomogeneousLocalizationAwayIntegrallyClosed
import MiyaokaMori.RingTheory.Polynomial.MvPolynomialIntegrallyClosed

/-! # Base change of the weighted coordinate chart ring: `A ⊗_k k[x]_(x_i) ≅ A[x]_(x_i)`

This is step 3 of the normality proof for the weighted chart products (`WeightedProjChartProdNormal.lean`), the
degree-zero tensor identification of the localization away from a coordinate
(`WeightedAwayBaseChange.equiv`).

Setting: `k` a field, `A` a `k`-algebra, `σ` any index type, `w : σ → ℕ` weights,
`𝒜 := weightedHomogeneousSubmodule k w` the weighted grading on `k[x] := MvPolynomial σ k`,
`ℬ` the same grading on `A[x]`, `B_k := HomogeneousLocalization.Away 𝒜 (X i) = k[x]_(x_i)` and
`B_A := Away ℬ (X i) = A[x]_(x_i)` (degree-zero parts of the localizations at `x_i`).
`B_k` carries a `k`-algebra structure given by `k → 𝒜 0 → B_k` (hypothesis `hk`, so that the
statement does not depend on which syntactic instance the caller uses).

## Natural-language proof (self-contained)

* `Φ : A ⊗_k B_k → B_A`, `a ⊗ b ↦ (a/1) · ι(b)`, where `ι : B_k → B_A` is induced by the graded
  ring hom `k[x] → A[x]` (coefficient extension; `HomogeneousLocalization.map`).
* **Surjective**: an element of `B_A` is `p / x_i^n` with `p ∈ ℬ(n·w_i)` weighted homogeneous.
  Writing `p = Σ_m c_m x^m` over its support, each monomial `x^m` has weight `n·w_i`, so
  `x^m / x_i^n ∈ B_k` and `p / x_i^n = Σ_m Φ(c_m ⊗ x^m/x_i^n)`.
* **Injective**: consider the square
  `A ⊗_k B_k --Φ--> B_A`, `A ⊗_k L_k --Ψ--> L_A`, with `L := Localization.Away (X i)` and the
  vertical maps `id ⊗ val` and `val`. It commutes (`val_Φ`). `id ⊗ val` is injective because `A`
  is flat over the field `k` (`Module.Flat.lTensor_preserves_injective_linearMap`). `Ψ` is
  injective because it has a left inverse `θ : L_A → A ⊗_k L_k` given by the universal property of
  the localization `A[x] → A[x]_{x_i}` applied to `A[x] ≅ A ⊗_k k[x] → A ⊗_k L_k`
  (`MvPolynomial.algebraTensorAlgEquiv`, `IsLocalization.Away.lift`); `θ ∘ Ψ = id` is checked on
  pure tensors `a ⊗ p/x_i^n`. Since `val` is injective on `B_A`, `Φ` is injective.
* Consequently `A ⊗_k B_k` is a domain / integrally closed as soon as `B_A` is
  (`tensor_isDomain`, `tensor_isIntegrallyClosed`); the latter facts about `B_A` are
  the integral closedness of the homogeneous localization away from a coordinate, applied to the integrally closed domain
  `A[x]` (`MvPolynomial.isIntegrallyClosed`, any `σ`).

Source: Stacks 030A for "polynomial rings over normal domains are normal"; the base-change
identification is elementary (EGA II 2.1 style bookkeeping), no literature tag.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open TensorProduct

attribute [local instance] MvPolynomial.weightedGradedAlgebra

noncomputable section

namespace MvPolynomial

/-- `MvPolynomial.map` preserves weighted homogeneity (coefficientwise). -/
theorem map_mem_weightedHomogeneousSubmodule {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (w : σ → ℕ) {n : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedHomogeneousSubmodule R w n) :
    MvPolynomial.map f p ∈ weightedHomogeneousSubmodule S w n := by
  rw [mem_weightedHomogeneousSubmodule] at hp ⊢
  intro m hm
  rw [coeff_map] at hm
  exact hp fun h => hm (by rw [h, map_zero])

end MvPolynomial

namespace WeightedAwayBaseChange

variable (k : Type u) [Field k] {σ : Type u} (w : σ → ℕ) (A : Type u) [CommRing A] [Algebra k A]

/-- The coefficient extension `k[x] → A[x]` as a graded ring hom for the weighted gradings. -/
def gradedMap : MvPolynomial.weightedHomogeneousSubmodule k w →+*ᵍ
    MvPolynomial.weightedHomogeneousSubmodule A w where
  toRingHom := MvPolynomial.map (algebraMap k A)
  map_mem h := MvPolynomial.map_mem_weightedHomogeneousSubmodule _ w h

@[simp] theorem gradedMap_apply (p : MvPolynomial σ k) :
    gradedMap k w A p = MvPolynomial.map (algebraMap k A) p := rfl

variable (i : σ)

theorem powers_le_comap_gradedMap :
    Submonoid.powers (MvPolynomial.X i : MvPolynomial σ k) ≤
      (Submonoid.powers (MvPolynomial.X i : MvPolynomial σ A)).comap (gradedMap k w A) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/-- `k[x]_(x_i) → A[x]_(x_i)`, the induced map on degree-zero homogeneous localizations. -/
def awayHom : HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i) →+*
    HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule A w)
      (MvPolynomial.X i) :=
  HomogeneousLocalization.map (gradedMap k w A) (powers_le_comap_gradedMap k w A i)

theorem powers_le_comap_map :
    Submonoid.powers (MvPolynomial.X i : MvPolynomial σ k) ≤
      (Submonoid.powers (MvPolynomial.X i : MvPolynomial σ A)).comap
        (MvPolynomial.map (algebraMap k A)) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/-- `k[x]_{x_i} → A[x]_{x_i}` on the ordinary localizations. -/
def locHom : Localization.Away (MvPolynomial.X i : MvPolynomial σ k) →+*
    Localization.Away (MvPolynomial.X i : MvPolynomial σ A) :=
  IsLocalization.map _ (MvPolynomial.map (algebraMap k A)) (powers_le_comap_map k A i)

theorem val_awayHom (x : HomogeneousLocalization.Away
    (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i)) :
    (awayHom k w A i x).val = locHom k A i x.val := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  rw [awayHom, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, locHom, Localization.mk_eq_mk', Localization.mk_eq_mk',
    IsLocalization.map_mk']
  rfl

/-- `f/1` for `f` of degree zero has value `algebraMap f` in the localization. -/
theorem val_fromZeroRingHom {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜] (P : Submonoid B) (x : 𝒜 0) :
    (HomogeneousLocalization.fromZeroRingHom 𝒜 P x).val = algebraMap B (Localization P) x := by
  show (HomogeneousLocalization.mk _).val = _
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.mk'_one _ _

/-- The coefficient map `A → A[x]_(x_i)`, `a ↦ a/1`. -/
def coeffHom : A →+* HomogeneousLocalization.Away
    (MvPolynomial.weightedHomogeneousSubmodule A w) (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom _ _).comp
    (algebraMap A (MvPolynomial.weightedHomogeneousSubmodule A w 0))

theorem val_coeffHom (a : A) : (coeffHom w A i a).val =
    algebraMap (MvPolynomial σ A) (Localization.Away (MvPolynomial.X i : MvPolynomial σ A))
      (MvPolynomial.C a) := by
  rw [coeffHom, RingHom.comp_apply, val_fromZeroRingHom]
  rfl

section Algebra

variable [Algebra k (HomogeneousLocalization.Away
    (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i))]
  (hk : algebraMap k (HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i)) =
    (HomogeneousLocalization.fromZeroRingHom _ _).comp
      (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0)))

/-- The `k`-algebra structure on `A[x]_(x_i)` through `k → A → A[x]_(x_i)`. -/
@[instance_reducible]
def baAlgebra : Algebra k (HomogeneousLocalization.Away
    (MvPolynomial.weightedHomogeneousSubmodule A w) (MvPolynomial.X i)) :=
  ((coeffHom w A i).comp (algebraMap k A)).toAlgebra

attribute [local instance] baAlgebra

/-- `coeffHom` as a `k`-algebra hom. -/
def coeffAlgHom : A →ₐ[k] HomogeneousLocalization.Away
    (MvPolynomial.weightedHomogeneousSubmodule A w) (MvPolynomial.X i) :=
  { coeffHom w A i with commutes' := fun _ => rfl }

include hk in
theorem awayHom_algebraMap (c : k) :
    awayHom k w A i (algebraMap k _ c) = algebraMap k _ c := by
  apply HomogeneousLocalization.val_injective
  rw [val_awayHom, hk, RingHom.comp_apply, val_fromZeroRingHom, locHom, IsLocalization.map_eq]
  show _ = (coeffHom w A i (algebraMap k A c)).val
  rw [val_coeffHom]
  congr 1
  simp

/-- `awayHom` as a `k`-algebra hom. -/
def awayAlgHom : HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) →ₐ[k]
    HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule A w) (MvPolynomial.X i) :=
  { awayHom k w A i with commutes' := awayHom_algebraMap k w A i hk }

/-- The comparison map `A ⊗_k k[x]_(x_i) → A[x]_(x_i)`. -/
def Φ : A ⊗[k] HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) →ₐ[k]
    HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule A w) (MvPolynomial.X i) :=
  Algebra.TensorProduct.productMap (coeffAlgHom k w A i) (awayAlgHom k w A i hk)

theorem Φ_tmul (a : A) (b : HomogeneousLocalization.Away
    (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i)) :
    Φ k w A i hk (a ⊗ₜ b) = coeffHom w A i a * awayHom k w A i b := rfl

/-- `val` as a `k`-linear map `k[x]_(x_i) → k[x]_{x_i}`. -/
def valLinear : HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) →ₗ[k]
    Localization.Away (MvPolynomial.X i : MvPolynomial σ k) where
  toFun := HomogeneousLocalization.val
  map_add' := HomogeneousLocalization.val_add
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, HomogeneousLocalization.val_mul, hk, RingHom.comp_apply,
      val_fromZeroRingHom, Algebra.smul_def, SetLike.GradeZero.coe_algebraMap,
      ← IsScalarTower.algebraMap_apply]

theorem valLinear_apply (x) : valLinear k w i hk x = x.val := rfl

/-- `locHom` as a `k`-algebra hom. -/
def locAlgHom : Localization.Away (MvPolynomial.X i : MvPolynomial σ k) →ₐ[k]
    Localization.Away (MvPolynomial.X i : MvPolynomial σ A) :=
  { locHom k A i with
    commutes' := fun c => by
      show locHom k A i (algebraMap k _ c) = algebraMap k _ c
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial σ k)
        (Localization.Away (MvPolynomial.X i : MvPolynomial σ k)), locHom, IsLocalization.map_eq,
        IsScalarTower.algebraMap_apply k (MvPolynomial σ A)
        (Localization.Away (MvPolynomial.X i : MvPolynomial σ A))]
      congr 1
      simp }

/-- `A → A[x] → A[x]_{x_i}` as a `k`-algebra hom. -/
def coeffLocAlgHom : A →ₐ[k] Localization.Away (MvPolynomial.X i : MvPolynomial σ A) :=
  (IsScalarTower.toAlgHom k (MvPolynomial σ A) _).comp
    ((Algebra.ofId A (MvPolynomial σ A)).restrictScalars k)

theorem coeffLocAlgHom_apply (a : A) : coeffLocAlgHom k A i a =
    algebraMap (MvPolynomial σ A) (Localization.Away (MvPolynomial.X i : MvPolynomial σ A))
      (MvPolynomial.C a) := rfl

/-- The comparison map on ordinary localizations `A ⊗_k k[x]_{x_i} → A[x]_{x_i}`. -/
def Ψ : A ⊗[k] Localization.Away (MvPolynomial.X i : MvPolynomial σ k) →ₐ[k]
    Localization.Away (MvPolynomial.X i : MvPolynomial σ A) :=
  Algebra.TensorProduct.productMap (coeffLocAlgHom k A i) (locAlgHom k A i)

theorem Ψ_tmul (a : A) (l : Localization.Away (MvPolynomial.X i : MvPolynomial σ k)) :
    Ψ k A i (a ⊗ₜ l) =
      algebraMap (MvPolynomial σ A) (Localization.Away (MvPolynomial.X i : MvPolynomial σ A))
        (MvPolynomial.C a) * locHom k A i l := rfl

theorem val_Φ (z : A ⊗[k] HomogeneousLocalization.Away
    (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i)) :
    (Φ k w A i hk z).val = Ψ k A i (LinearMap.lTensor A (valLinear k w i hk) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [HomogeneousLocalization.val_zero]
  | tmul a b =>
    rw [Φ_tmul, LinearMap.lTensor_tmul, Ψ_tmul, HomogeneousLocalization.val_mul, val_coeffHom,
      val_awayHom, valLinear_apply]
  | add x y hx hy => rw [map_add, HomogeneousLocalization.val_add, map_add, map_add, hx, hy]

/-- `A[x] → A ⊗_k k[x]_{x_i}`, used to build the inverse of `Ψ`. -/
def ρ : MvPolynomial σ A →+* A ⊗[k] Localization.Away (MvPolynomial.X i : MvPolynomial σ k) :=
  (Algebra.TensorProduct.map (AlgHom.id k A)
    (IsScalarTower.toAlgHom k (MvPolynomial σ k) _)).toRingHom.comp
    (MvPolynomial.algebraTensorAlgEquiv k A).symm.toAlgHom.toRingHom

theorem ρ_map (p : MvPolynomial σ k) : ρ k A i (MvPolynomial.map (algebraMap k A) p) =
    1 ⊗ₜ algebraMap (MvPolynomial σ k) (Localization.Away (MvPolynomial.X i : MvPolynomial σ k)) p := by
  simp [ρ, Algebra.TensorProduct.map_tmul]

theorem ρ_C (a : A) : ρ k A i (MvPolynomial.C a) = a ⊗ₜ 1 := by
  rw [MvPolynomial.C_apply]
  show (Algebra.TensorProduct.map _ _)
    ((MvPolynomial.algebraTensorAlgEquiv k A).symm (MvPolynomial.monomial 0 a)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_monomial, Algebra.TensorProduct.map_tmul]
  simp

theorem ρ_X_isUnit : IsUnit (ρ k A i (MvPolynomial.X i)) := by
  have h := ρ_map k A i (MvPolynomial.X i)
  rw [MvPolynomial.map_X] at h
  rw [h]
  exact (IsLocalization.Away.algebraMap_isUnit (MvPolynomial.X i)).map
    (Algebra.TensorProduct.includeRight (R := k) (A := A))

/-- The inverse of `Ψ`: `A[x]_{x_i} → A ⊗_k k[x]_{x_i}`. -/
def θ : Localization.Away (MvPolynomial.X i : MvPolynomial σ A) →+*
    A ⊗[k] Localization.Away (MvPolynomial.X i : MvPolynomial σ k) :=
  IsLocalization.Away.lift (MvPolynomial.X i) (ρ_X_isUnit k A i)

theorem θ_Ψ (z : A ⊗[k] Localization.Away (MvPolynomial.X i : MvPolynomial σ k)) :
    θ k A i (Ψ k A i z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    obtain ⟨⟨p, y⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (MvPolynomial.X i : MvPolynomial σ k)) l
    have key : ∀ (q : MvPolynomial σ k)
        (y : Submonoid.powers (MvPolynomial.X i : MvPolynomial σ k)),
        IsLocalization.Away.lift (MvPolynomial.X i) (ρ_X_isUnit k A i)
          (IsLocalization.mk' (Localization.Away (MvPolynomial.X i : MvPolynomial σ A))
            (MvPolynomial.map (algebraMap k A) q)
            (⟨MvPolynomial.map (algebraMap k A) y, powers_le_comap_map k A i y.2⟩ :
              Submonoid.powers (MvPolynomial.X i : MvPolynomial σ A))) =
          1 ⊗ₜ IsLocalization.mk' (Localization.Away (MvPolynomial.X i : MvPolynomial σ k)) q y := by
      intro q y
      unfold IsLocalization.Away.lift
      rw [IsLocalization.lift_mk'_spec]
      show ρ k A i _ = ρ k A i _ * _
      rw [ρ_map, ρ_map, Algebra.TensorProduct.tmul_mul_tmul, mul_one, IsLocalization.mk'_spec']
    rw [Ψ_tmul, map_mul, θ, IsLocalization.Away.lift_eq, ρ_C, locHom, IsLocalization.map_mk', key,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem Ψ_injective : Function.Injective (Ψ k A i) :=
  Function.LeftInverse.injective (θ_Ψ k A i)

theorem Φ_injective : Function.Injective (Φ k w A i hk) := by
  intro z₁ z₂ hz
  have h := congrArg HomogeneousLocalization.val hz
  rw [val_Φ, val_Φ] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := A) (valLinear k w i hk)
    (HomogeneousLocalization.val_injective _) (Ψ_injective k A i h)

theorem X_mem_weighted (R : Type*) [CommRing R] (j : σ) :
    (MvPolynomial.X j : MvPolynomial σ R) ∈ MvPolynomial.weightedHomogeneousSubmodule R w (w j) :=
  (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (MvPolynomial.isWeightedHomogeneous_X R w j)

theorem Φ_surjective : Function.Surjective (Φ k w A i hk) := by
  intro y
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem_weighted w A i) y
  let T : Subring (Localization.Away (MvPolynomial.X i : MvPolynomial σ A)) :=
    ((algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial σ A))).comp
      (Φ k w A i hk).toRingHom).range
  suffices h : (HomogeneousLocalization.Away.mk _ (X_mem_weighted w A i) n p hp).val ∈ T by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, HomogeneousLocalization.val_injective _ hz⟩
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  have hp' := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hp
  rw [MvPolynomial.as_sum p, map_sum, Finset.sum_mul]
  refine Subring.sum_mem _ fun m hm => ?_
  have hweight := hp' (MvPolynomial.mem_support_iff.mp hm)
  have hmono : (MvPolynomial.monomial m 1 : MvPolynomial σ k) ∈
      MvPolynomial.weightedHomogeneousSubmodule k w (n • w i) :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_monomial w m 1 hweight)
  refine ⟨MvPolynomial.coeff m p ⊗ₜ
    HomogeneousLocalization.Away.mk _ (X_mem_weighted w k i) n (MvPolynomial.monomial m 1) hmono, ?_⟩
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    HomogeneousLocalization.algebraMap_apply]
  rw [Φ_tmul, HomogeneousLocalization.val_mul, val_coeffHom, val_awayHom,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', locHom, IsLocalization.map_mk',
    IsLocalization.mk'_eq_mul_mk'_one, ← mul_assoc, ← map_mul, MvPolynomial.map_monomial, map_one,
    MvPolynomial.C_mul_monomial, mul_one]
  congr 1
  rw [IsLocalization.mk'_eq_iff_eq]
  simp

/-- **The base-change isomorphism** `A ⊗_k k[x]_(x_i) ≃+* A[x]_(x_i)`. -/
def equiv : A ⊗[k] HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) ≃+*
    HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule A w) (MvPolynomial.X i) :=
  RingEquiv.ofBijective (Φ k w A i hk) ⟨Φ_injective k w A i hk, Φ_surjective k w A i hk⟩

include hk in
/-- `A ⊗_k k[x]_(x_i)` is a domain when `A` is (it is `A[x]_(x_i)`). -/
theorem tensor_isDomain [IsDomain A] :
    IsDomain (A ⊗[k] HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i)) :=
  haveI := HomogeneousLocalization.Away.isDomain
    (MvPolynomial.weightedHomogeneousSubmodule A w) (MvPolynomial.X_ne_zero (R := A) i)
  (equiv k w A i hk).toMulEquiv.isDomain _

include hk in
/-- `A ⊗_k k[x]_(x_i)` is integrally closed when `A` is an integrally closed domain
(it is `A[x]_(x_i)`, the degree-zero homogeneous localization of the integrally closed domain
`A[x]`). -/
theorem tensor_isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A] (hwi : 0 < w i) :
    IsIntegrallyClosed (A ⊗[k] HomogeneousLocalization.Away
      (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i)) :=
  haveI := MvPolynomial.isIntegrallyClosed σ A
  haveI := HomogeneousLocalization.Away.isIntegrallyClosed_of_isIntegrallyClosed
    (MvPolynomial.weightedHomogeneousSubmodule A w) hwi (X_mem_weighted w A i)
    (MvPolynomial.X_ne_zero i)
  IsIntegrallyClosed.of_equiv (equiv k w A i hk).symm

end Algebra

end WeightedAwayBaseChange

end
