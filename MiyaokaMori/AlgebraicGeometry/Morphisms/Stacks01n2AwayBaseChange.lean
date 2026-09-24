import MiyaokaMori.Prelude

/-! # Base change of the affine charts of Proj

**Algebraic core of Stacks 01N2** (`constructions-lemma-base-change-map-proj`; EGA II 2.8.10).

Setting: `R → R'`, `A` a graded `R`-algebra (`𝒜 : ℕ → Submodule R A`), `B` a graded `R'`-algebra
(`ℬ : ℕ → Submodule R' B`), `f : 𝒜 →+*ᵍ ℬ` a graded ring hom which is the base change of `R → R'`:
`fR : A →ₐ[R] B` with `fR = f` and `IsBaseChange R' fR` (i.e. `B = R' ⊗_R A`).

Results:
* `pieceLift_bijective`: for every degree `m` the canonical map `R' ⊗_R 𝒜_m → ℬ_m` is bijective, i.e.
  every graded piece of `B` is the base change of the corresponding graded piece of `A`
  (`pieceMap_isBaseChange`).
* `awayLift_bijective` / `isBaseChange_away`: for `s ∈ 𝒜_i` homogeneous, the degree-zero homogeneous
  localization `ℬ_(f s) = (B_{f s})_0` is the base change of `𝒜_(s) = (A_s)_0` along `R → R'`, via
  `HomogeneousLocalization.Away.map f s`.
* `isPushout_away`: the corresponding pushout square of commutative rings
  `R → 𝒜_(s)`, `R → R'`, `𝒜_(s) → ℬ_(f s)`, `R' → ℬ_(f s)` in `CommRingCat`. This is what
  `Proj.isPullback_of_isBaseChange` (`Stacks01n2.lean`) needs on the affine chart `D₊(s)`.

## Natural-language proof

Graded pieces. Let `e : R' ⊗_R A ≃ B`, `r ⊗ a ↦ r • f a`, be the base-change isomorphism (`hbc.equiv`).
The `R`-linear projection `π_m : A → 𝒜_m` onto the degree-`m` component (`DirectSum.decompose`) is a
retraction of the inclusion `ι_m : 𝒜_m → A`, so `id ⊗ ι_m : R' ⊗ 𝒜_m → R' ⊗ A` is injective (it has the
left inverse `id ⊗ π_m`). Since `f` is graded, `f (π_m a) = π'_m (f a)` with `π'_m : B → ℬ_m`
(`GradedRingHom.map_directSumDecompose`), hence `e ∘ (id ⊗ (ι_m ∘ π_m)) = (ι'_m ∘ π'_m) ∘ e`.
The map `L_m : R' ⊗ 𝒜_m → ℬ_m`, `r ⊗ a ↦ r • f a`, satisfies `ι'_m ∘ L_m = e ∘ (id ⊗ ι_m)`, so it is
injective; for `b ∈ ℬ_m`, `L_m ((id ⊗ π_m) (e⁻¹ b)) = π'_m (e (e⁻¹ b)) = π'_m b = b`, so it is surjective.

Degree-zero localization. Write `mk_n : 𝒜_{ni} → 𝒜_(s)`, `a ↦ a / s^n` (`Away.mk`), similarly `mk'_n` for
`ℬ` and `f s`, and `L : R' ⊗_R 𝒜_(s) → ℬ_(f s)`, `r ⊗ q ↦ r • Away.map f s q`.
1. Compatibility: `L ∘ (id ⊗ mk_n) = mk'_n ∘ L_{ni}` (check on `r ⊗ a`: both give `r • (f a / (f s)^n)`).
2. Common denominators: every element of `R' ⊗_R 𝒜_(s)` is `(id ⊗ mk_n) t` for some `n` and
   `t ∈ R' ⊗ 𝒜_{ni}` (induction on the tensor; for a sum use `mk_{n₁+n₂} (s^{n₂} a) = mk_{n₁} a`).
3. Surjective: `y ∈ ℬ_(f s)` is `b / (f s)^n` with `b ∈ ℬ_{ni}`; by the graded-piece statement
   `b = L_{ni} t`, so `y = mk'_n (L_{ni} t) = L ((id ⊗ mk_n) t)`.
4. Injective: if `L ((id ⊗ mk_n) t) = 0` then `mk'_n (L_{ni} t) = 0`, i.e. `(f s)^N · L_{ni} t = 0` in `B`
   for some `N` (`IsLocalization.mk'_eq_zero_iff`). Multiplication by `s^N` (resp. `(f s)^N`) is a map
   `𝒜_{ni} → 𝒜_{(n+N)i}` compatible with `L`, so `L_{(n+N)i} ((id ⊗ s^N) t) = 0`, hence `(id ⊗ s^N) t = 0`
   by injectivity of `L_{(n+N)i}`, and `(id ⊗ mk_n) t = (id ⊗ mk_{n+N}) ((id ⊗ s^N) t) = 0`.
5. Hence `L` is an isomorphism and `IsBaseChange R' (Away.map f s)` (`IsBaseChange.of_equiv`), i.e.
   `Algebra.IsPushout R R' 𝒜_(s) ℬ_(f s)`; `CommRingCat.isPushout_of_isPushout` turns it into the pushout
   square in `CommRingCat`.

Edge cases: `s = 0` or `i = 0` are allowed (both localizations are then the zero ring resp. the
degree-`0` localization; the argument does not use `0 < i`). `R' = 0`: `B = 0`, all sides are zero rings.

Source: Stacks 01N2, proof of (1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

open HomogeneousLocalization Graded
open scoped TensorProduct

noncomputable section

namespace MiyaokaMori.Stacks01n2

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (fR : A →ₐ[R] B) (hfR : ∀ a, fR a = f a)

/-! ## Graded pieces -/

/-- The degree-`m` component `A →ₗ[R] 𝒜 m` of the decomposition. -/
def piece (m : ℕ) : A →ₗ[R] 𝒜 m where
  toFun a := DirectSum.decompose 𝒜 a m
  map_add' a b := by simp [DirectSum.decompose_add]
  map_smul' r a := by simp [DirectSum.decompose_smul, DirectSum.smul_apply]

theorem piece_apply (m : ℕ) (a : A) : (piece 𝒜 m a : A) = DirectSum.decompose 𝒜 a m := rfl

theorem piece_of_mem {m : ℕ} (a : 𝒜 m) : piece 𝒜 m a = a :=
  Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 a.2)

theorem piece_comp_subtype (m : ℕ) : piece 𝒜 m ∘ₗ (𝒜 m).subtype = LinearMap.id :=
  LinearMap.ext fun a => piece_of_mem 𝒜 a

omit [Algebra R R'] [IsScalarTower R R' B] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
include hfR in
theorem map_algebraMap (r : R) : f (algebraMap R A r) = algebraMap R B r := by
  rw [← hfR, fR.commutes]

/-- `f` restricted to the degree-`m` pieces, as an `R`-linear map (`ℬ m` is an `R`-module through
`R → R'`). -/
def pieceMap (m : ℕ) : 𝒜 m →ₗ[R] ℬ m where
  toFun a := ⟨f a, map_mem f a.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' r a := Subtype.ext (by
    simp only [Submodule.coe_smul, RingHom.id_apply, Submodule.coe_smul_of_tower, Algebra.smul_def,
      map_mul, map_algebraMap 𝒜 ℬ f fR hfR])

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem pieceMap_apply (m : ℕ) (a : 𝒜 m) : (pieceMap 𝒜 ℬ f fR hfR m a : B) = f a := rfl

theorem pieceMap_piece (m : ℕ) (a : A) :
    pieceMap 𝒜 ℬ f fR hfR m (piece 𝒜 m a) = piece ℬ m (fR a) := by
  apply Subtype.ext
  rw [pieceMap_apply, piece_apply, piece_apply, hfR, GradedRingHom.map_directSumDecompose]

/-- `R' ⊗[R] 𝒜 m → ℬ m`, `r ⊗ a ↦ r • f a`. -/
def pieceLift (m : ℕ) : R' ⊗[R] 𝒜 m →ₗ[R'] ℬ m :=
  (TensorProduct.isBaseChange R (𝒜 m) R').lift (pieceMap 𝒜 ℬ f fR hfR m)

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem pieceLift_one_tmul (m : ℕ) (a : 𝒜 m) :
    pieceLift 𝒜 ℬ f fR hfR m (1 ⊗ₜ a) = pieceMap 𝒜 ℬ f fR hfR m a :=
  IsBaseChange.lift_eq _ _ a

theorem pieceLift_tmul (m : ℕ) (r : R') (a : 𝒜 m) :
    pieceLift 𝒜 ℬ f fR hfR m (r ⊗ₜ a) = r • pieceMap 𝒜 ℬ f fR hfR m a := by
  have : r ⊗ₜ[R] a = r • ((1 : R') ⊗ₜ[R] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, pieceLift_one_tmul]

variable (hbc : IsBaseChange R' fR.toLinearMap)

include hbc in
theorem coe_pieceLift (m : ℕ) (t : R' ⊗[R] 𝒜 m) :
    (pieceLift 𝒜 ℬ f fR hfR m t : B) = hbc.equiv (((𝒜 m).subtype).baseChange R' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [pieceLift_tmul, LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul,
      Submodule.coe_smul_of_tower, pieceMap_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, hfR]
  | add x y hx hy => rw [map_add, map_add, map_add, Submodule.coe_add, hx, hy]

include f hfR hbc in
theorem equiv_baseChange_piece (m : ℕ) (t : R' ⊗[R] A) :
    hbc.equiv (((𝒜 m).subtype ∘ₗ piece 𝒜 m).baseChange R' t) = piece ℬ m (hbc.equiv t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul,
      LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    congr 1
    rw [hfR, ← pieceMap_apply 𝒜 ℬ f fR hfR, pieceMap_piece]
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

include hbc in
theorem pieceLift_injective (m : ℕ) : Function.Injective (pieceLift 𝒜 ℬ f fR hfR m) := by
  intro t₁ t₂ h
  have h1 : hbc.equiv (((𝒜 m).subtype).baseChange R' t₁) =
      hbc.equiv (((𝒜 m).subtype).baseChange R' t₂) := by
    rw [← coe_pieceLift 𝒜 ℬ f fR hfR hbc, ← coe_pieceLift 𝒜 ℬ f fR hfR hbc, h]
  have h2 := hbc.equiv.injective h1
  have key : ∀ t, (piece 𝒜 m).baseChange R' (((𝒜 m).subtype).baseChange R' t) = t := fun t => by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, piece_comp_subtype,
      LinearMap.baseChange_id, LinearMap.id_apply]
  rw [← key t₁, ← key t₂, h2]

include hbc in
theorem pieceLift_surjective (m : ℕ) : Function.Surjective (pieceLift 𝒜 ℬ f fR hfR m) := by
  intro b
  refine ⟨(piece 𝒜 m).baseChange R' (hbc.equiv.symm b), ?_⟩
  apply Subtype.ext
  rw [coe_pieceLift 𝒜 ℬ f fR hfR hbc, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    equiv_baseChange_piece 𝒜 ℬ f fR hfR hbc, LinearEquiv.apply_symm_apply, piece_of_mem]

include hbc in
theorem pieceLift_bijective (m : ℕ) : Function.Bijective (pieceLift 𝒜 ℬ f fR hfR m) :=
  ⟨pieceLift_injective 𝒜 ℬ f fR hfR hbc m, pieceLift_surjective 𝒜 ℬ f fR hfR hbc m⟩

include hbc in
/-- Every graded piece of `B = R' ⊗_R A` is the base change of the corresponding piece of `A`. -/
theorem pieceMap_isBaseChange (m : ℕ) : IsBaseChange R' (pieceMap 𝒜 ℬ f fR hfR m) :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ (pieceLift_bijective 𝒜 ℬ f fR hfR hbc m))
    fun a => by
      rw [LinearEquiv.ofBijective_apply, pieceLift_one_tmul]

/-! ## Degree-zero homogeneous localizations -/

section Away

variable {S : Type u} [CommRing S] {C : Type u} [CommRing C] [Algebra S C] (𝒞 : ℕ → Submodule S C)
  [GradedAlgebra 𝒞]

/-- `S → 𝒞 0 → 𝒞_(s)`: the structure map of the degree-zero localization over the base ring. -/
abbrev awayAlgebraMap (s : C) : S →+* Away 𝒞 s :=
  (fromZeroRingHom 𝒞 (Submonoid.powers s)).comp (algebraMap S (𝒞 0))

theorem val_awayAlgebraMap (s : C) (r : S) :
    (awayAlgebraMap 𝒞 s r).val = algebraMap C (Localization.Away s) (algebraMap S C r) := by
  change (HomogeneousLocalization.mk ⟨0, algebraMap S (𝒞 0) r, 1, one_mem _⟩).val = _
  rw [HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap]
  rfl

/-- The `S`-algebra structure on `𝒞_(s)` with structure map `awayAlgebraMap`; its scalar action is
Mathlib's `HomogeneousLocalization.instSMul` (`r • (a / t) = (r • a) / t`), so there is no diamond.
A local instance of this file. -/
@[instance_reducible] def awayAlgebra (s : C) : Algebra S (Away 𝒞 s) where
  toSMul := inferInstance
  algebraMap := awayAlgebraMap 𝒞 s
  commutes' _ _ := mul_comm _ _
  smul_def' r x := by
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective x
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, val_awayAlgebraMap,
      HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      one_mul, Localization.smul_mk, Algebra.smul_def]

attribute [local instance] awayAlgebra

theorem algebraMap_away_eq (s : C) : algebraMap S (Away 𝒞 s) = awayAlgebraMap 𝒞 s := rfl

variable {s : C} {i : ℕ} (hs : s ∈ 𝒞 i)

/-- `a ↦ a / s ^ n` on the degree-`n • i` piece, as an `S`-linear map. -/
def mkAway (n : ℕ) : 𝒞 (n • i) →ₗ[S] Away 𝒞 s where
  toFun a := Away.mk 𝒞 hs n a a.2
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, HomogeneousLocalization.val_add, Submodule.coe_add,
      Localization.add_mk_self]
  map_smul' r a := by
    apply HomogeneousLocalization.val_injective
    rw [RingHom.id_apply, HomogeneousLocalization.val_smul, Away.val_mk, Away.val_mk,
      Localization.smul_mk, Submodule.coe_smul]

theorem mkAway_apply (n : ℕ) (a : 𝒞 (n • i)) : mkAway 𝒞 hs n a = Away.mk 𝒞 hs n a a.2 := rfl

/-- Multiplication by `s ^ k`, `𝒞 (n • i) → 𝒞 (m • i)` for `m = n + k`. -/
def mulPow (k : ℕ) {n m : ℕ} (h : m = n + k) : 𝒞 (n • i) →ₗ[S] 𝒞 (m • i) where
  toFun a := ⟨s ^ k * a, by
    rw [h, add_smul, add_comm]
    exact SetLike.mul_mem_graded (SetLike.pow_mem_graded k hs) a.2⟩
  map_add' a b := Subtype.ext (by simp [mul_add])
  map_smul' r a := Subtype.ext (by simp)

theorem coe_mulPow (k : ℕ) {n m : ℕ} (h : m = n + k) (a : 𝒞 (n • i)) :
    (mulPow 𝒞 hs k h a : C) = s ^ k * a := rfl

theorem mkAway_mulPow (k : ℕ) {n m : ℕ} (h : m = n + k) (a : 𝒞 (n • i)) :
    mkAway 𝒞 hs m (mulPow 𝒞 hs k h a) = mkAway 𝒞 hs n a := by
  apply HomogeneousLocalization.val_injective
  rw [mkAway_apply, mkAway_apply, Away.val_mk, Away.val_mk, coe_mulPow, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  subst h
  rw [pow_add]
  ring

theorem mkAway_comp_mulPow (k : ℕ) {n m : ℕ} (h : m = n + k) :
    mkAway 𝒞 hs m ∘ₗ mulPow 𝒞 hs k h = mkAway 𝒞 hs n :=
  LinearMap.ext (mkAway_mulPow 𝒞 hs k h)

theorem exists_pow_mul_eq_zero_of_mkAway_eq_zero {n : ℕ} (b : 𝒞 (n • i))
    (h : mkAway 𝒞 hs n b = 0) : ∃ N : ℕ, s ^ N * (b : C) = 0 := by
  have hv := congrArg HomogeneousLocalization.val h
  rw [HomogeneousLocalization.val_zero, mkAway_apply, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff] at hv
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := hv
  exact ⟨N, hN⟩

variable {T : Type u} [CommRing T] [Algebra S T]

theorem baseChange_mkAway_mulPow (k : ℕ) {n m : ℕ} (h : m = n + k) (a : T ⊗[S] 𝒞 (n • i)) :
    (mkAway 𝒞 hs m).baseChange T ((mulPow 𝒞 hs k h).baseChange T a) =
      (mkAway 𝒞 hs n).baseChange T a := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, mkAway_comp_mulPow]

/-- Common denominators: every element of `T ⊗[S] 𝒞_(s)` comes from some `T ⊗[S] 𝒞 (n • i)`. -/
theorem exists_baseChange_mkAway (t : T ⊗[S] Away 𝒞 s) :
    ∃ (n : ℕ) (a : T ⊗[S] 𝒞 (n • i)), (mkAway 𝒞 hs n).baseChange T a = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul r q =>
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒞 hs q
    exact ⟨n, r ⊗ₜ ⟨a, ha⟩, by rw [LinearMap.baseChange_tmul]; rfl⟩
  | add t₁ t₂ ih₁ ih₂ =>
    obtain ⟨n₁, a₁, rfl⟩ := ih₁
    obtain ⟨n₂, a₂, rfl⟩ := ih₂
    refine ⟨n₁ + n₂, (mulPow 𝒞 hs n₂ rfl).baseChange T a₁ +
      (mulPow 𝒞 hs n₁ (add_comm n₁ n₂)).baseChange T a₂, ?_⟩
    rw [map_add, baseChange_mkAway_mulPow, baseChange_mkAway_mulPow]

end Away

section AwayBaseChange

attribute [local instance] awayAlgebra

variable {s : A} {i : ℕ}

/-- `R → R' → ℬ_(f s)` as an `R`-algebra structure on `ℬ_(f s)` (local instance). -/
@[instance_reducible] def awayAlgebraBR : Algebra R (Away ℬ (f s)) :=
  ((awayAlgebraMap ℬ (f s)).comp (algebraMap R R')).toAlgebra

/-- `Away.map f s` as an algebra structure `𝒜_(s) → ℬ_(f s)` (local instance). -/
@[instance_reducible] def awayAlgebraAB : Algebra (Away 𝒜 s) (Away ℬ (f s)) :=
  (Away.map f s).toAlgebra

attribute [local instance] awayAlgebraBR awayAlgebraAB

theorem isScalarTower_R_R' : IsScalarTower R R' (Away ℬ (f s)) :=
  @IsScalarTower.of_algebraMap_eq R R' (Away ℬ (f s)) _ _ _ _ (awayAlgebra ℬ (f s))
    (awayAlgebraBR 𝒜 ℬ f) fun _ => rfl

attribute [local instance] isScalarTower_R_R'

include hfR in
theorem awayMap_awayAlgebraMap (r : R) :
    Away.map f s (awayAlgebraMap 𝒜 s r) = awayAlgebraMap ℬ (f s) (algebraMap R R' r) := by
  apply HomogeneousLocalization.val_injective
  rw [val_awayAlgebraMap, ← Localization.mk_one_eq_algebraMap]
  change (HomogeneousLocalization.map f _ (HomogeneousLocalization.mk
    ⟨0, algebraMap R (𝒜 0) r, 1, one_mem _⟩)).val = _
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  simp only [SetLike.GradeZero.coe_algebraMap, map_algebraMap 𝒜 ℬ f fR hfR,
    ← IsScalarTower.algebraMap_apply]
  congr 1
  exact Subtype.ext (map_one f)

include hfR in
/-- Not an instance: it depends on the base-change data `fR`, `hfR`; supply it with `haveI`. -/
theorem isScalarTower_R_A : IsScalarTower R (Away 𝒜 s) (Away ℬ (f s)) :=
  @IsScalarTower.of_algebraMap_eq R (Away 𝒜 s) (Away ℬ (f s)) _ _ _ (awayAlgebra 𝒜 s)
    (awayAlgebraAB 𝒜 ℬ f) (awayAlgebraBR 𝒜 ℬ f) fun r => (awayMap_awayAlgebraMap 𝒜 ℬ f fR hfR r).symm

/-- `R' ⊗[R] 𝒜_(s) → ℬ_(f s)`, `r ⊗ q ↦ r • Away.map f s q`. -/
def awayLift : R' ⊗[R] Away 𝒜 s →ₗ[R'] Away ℬ (f s) :=
  haveI := isScalarTower_R_A 𝒜 ℬ f fR hfR (s := s)
  (TensorProduct.isBaseChange R (Away 𝒜 s) R').lift
    (IsScalarTower.toAlgHom R (Away 𝒜 s) (Away ℬ (f s))).toLinearMap

theorem awayLift_one_tmul (q : Away 𝒜 s) :
    awayLift 𝒜 ℬ f fR hfR (s := s) (1 ⊗ₜ q) = Away.map f s q :=
  haveI := isScalarTower_R_A 𝒜 ℬ f fR hfR (s := s)
  IsBaseChange.lift_eq _ _ q

theorem awayLift_tmul (r : R') (q : Away 𝒜 s) :
    awayLift 𝒜 ℬ f fR hfR (s := s) (r ⊗ₜ q) = r • Away.map f s q := by
  have : r ⊗ₜ[R] q = r • ((1 : R') ⊗ₜ[R] q) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, awayLift_one_tmul]

variable (hs : s ∈ 𝒜 i)

theorem awayLift_baseChange_mkAway (n : ℕ) (a : R' ⊗[R] 𝒜 (n • i)) :
    awayLift 𝒜 ℬ f fR hfR ((mkAway 𝒜 hs n).baseChange R' a) =
      mkAway ℬ (map_mem f hs) n (pieceLift 𝒜 ℬ f fR hfR (n • i) a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, awayLift_tmul, pieceLift_tmul, map_smul, mkAway_apply,
      mkAway_apply, Away.map_mk]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem pieceLift_baseChange_mulPow (k : ℕ) {n m : ℕ} (h : m = n + k) (a : R' ⊗[R] 𝒜 (n • i)) :
    pieceLift 𝒜 ℬ f fR hfR (m • i) ((mulPow 𝒜 hs k h).baseChange R' a) =
      mulPow ℬ (map_mem f hs) k h (pieceLift 𝒜 ℬ f fR hfR (n • i) a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, pieceLift_tmul, pieceLift_tmul, map_smul]
    congr 1
    apply Subtype.ext
    rw [pieceMap_apply, coe_mulPow, coe_mulPow, pieceMap_apply, map_mul, map_pow]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

include hs hbc in
theorem awayLift_injective : Function.Injective (awayLift 𝒜 ℬ f fR hfR (s := s)) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨n, a, rfl⟩ := exists_baseChange_mkAway 𝒜 hs t
  rw [awayLift_baseChange_mkAway 𝒜 ℬ f fR hfR hs] at ht
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_mkAway_eq_zero ℬ (map_mem f hs) _ ht
  have h1 : mulPow ℬ (map_mem f hs) N rfl (pieceLift 𝒜 ℬ f fR hfR (n • i) a) = 0 :=
    Subtype.ext (by rw [coe_mulPow]; exact hN)
  rw [← pieceLift_baseChange_mulPow 𝒜 ℬ f fR hfR hs] at h1
  have h2 := pieceLift_injective 𝒜 ℬ f fR hfR hbc ((n + N) • i) (h1.trans (map_zero _).symm)
  rw [← baseChange_mkAway_mulPow 𝒜 hs N rfl a, h2, map_zero]

include hs hbc in
theorem awayLift_surjective : Function.Surjective (awayLift 𝒜 ℬ f fR hfR (s := s)) := by
  intro y
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (map_mem f hs) y
  obtain ⟨a, ha⟩ := pieceLift_surjective 𝒜 ℬ f fR hfR hbc (n • i) ⟨b, hb⟩
  refine ⟨(mkAway 𝒜 hs n).baseChange R' a, ?_⟩
  rw [awayLift_baseChange_mkAway 𝒜 ℬ f fR hfR hs, ha]
  rfl

include hs hbc in
theorem awayLift_bijective : Function.Bijective (awayLift 𝒜 ℬ f fR hfR (s := s)) :=
  ⟨awayLift_injective 𝒜 ℬ f fR hfR hbc hs, awayLift_surjective 𝒜 ℬ f fR hfR hbc hs⟩

include hs hbc in
/-- **Stacks 01N2, algebraic core**: `ℬ_(f s) = R' ⊗_R 𝒜_(s)` for `s ∈ 𝒜 i` homogeneous. -/
theorem isBaseChange_away :
    haveI := isScalarTower_R_A 𝒜 ℬ f fR hfR (s := s)
    IsBaseChange R' (IsScalarTower.toAlgHom R (Away 𝒜 s) (Away ℬ (f s))).toLinearMap :=
  haveI := isScalarTower_R_A 𝒜 ℬ f fR hfR (s := s)
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ (awayLift_bijective 𝒜 ℬ f fR hfR hbc hs))
    fun q => by rw [LinearEquiv.ofBijective_apply, awayLift_one_tmul]; rfl

include hs hbc in
theorem algebra_isPushout_away :
    haveI := isScalarTower_R_A 𝒜 ℬ f fR hfR (s := s)
    Algebra.IsPushout R R' (Away 𝒜 s) (Away ℬ (f s)) :=
  haveI := isScalarTower_R_A 𝒜 ℬ f fR hfR (s := s)
  ⟨isBaseChange_away 𝒜 ℬ f fR hfR hbc hs⟩

include hfR hbc hs in
/-- **Stacks 01N2, algebraic core in `CommRingCat`**: the square
`R → 𝒜_(s)`, `R → R'`, `𝒜_(s) → ℬ_(f s)` (`Away.map f s`), `R' → ℬ_(f s)` is a pushout. -/
theorem isPushout_away :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom ((fromZeroRingHom 𝒜 (Submonoid.powers s)).comp (algebraMap R (𝒜 0))))
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (Away.map f s))
      (CommRingCat.ofHom ((fromZeroRingHom ℬ (Submonoid.powers (f s))).comp
        (algebraMap R' (ℬ 0)))) := by
  have := isScalarTower_R_A 𝒜 ℬ f fR hfR (s := s)
  have := (algebra_isPushout_away 𝒜 ℬ f fR hfR hbc hs).symm
  exact CommRingCat.isPushout_of_isPushout R (Away 𝒜 s) R' (Away ℬ (f s))

end AwayBaseChange

end MiyaokaMori.Stacks01n2

end
