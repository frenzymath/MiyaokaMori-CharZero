import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01n2AwayBaseChange

/-! # Chart-level algebra of Stacks 01N2 for the twisting sheaves

**Chart-level algebra of Stacks 01N2 for the twisting sheaves** (degree-`n` analogue of
`Stacks01n2AwayBaseChange`).

Setting as in `Stacks01n2AwayBaseChange.lean`: `R → R'`, `𝒜 : ℕ → Submodule R A`, `ℬ : ℕ → Submodule R' B`
graded, `f : 𝒜 →+*ᵍ ℬ` the base change of `R → R'` (`fR : A →ₐ[R] B`, `fR = f`,
`hbc : IsBaseChange R' fR`, i.e. `B = R' ⊗_R A`), `s ∈ 𝒜 i` homogeneous of positive degree `i`, `n : ℤ`.

* `twistAway 𝒞 hs hi n`: the degree-`n` part `(C_s)_n` of the localization `C_s`, i.e. the fractions `a / s ^ k`
  with `a ∈ 𝒞 p`, `p = k i + n`, as a submodule of `Localization.Away s` (this is the module of sections of
  `O_{Proj 𝒞}(n)` over `D₊(s)`; the sheaf-theoretic identification is in `Stacks01n2TwistStalkSections.lean`).
  `mkTwist p k hp : 𝒞 p → (C_s)_n`, `a ↦ a / s ^ k`; `mulPowTwist N : 𝒞 p → 𝒞 (N i + p)`, `a ↦ s ^ N a`;
  `exists_baseChange_mkTwist` (common denominators in `T ⊗ (C_s)_n`);
  `exists_pow_mul_eq_zero_of_mkTwist_eq_zero` (`a / s ^ k = 0 ↔ s ^ N a = 0` for some `N`);
  `val_mul_mem` (`(C_s)_n` is stable under multiplication by `𝒞_(s) = (C_s)_0`).
* `twistAwayMap : (A_s)_n →ₗ[R] (B_{f s})_n`, `a / s ^ k ↦ f a / (f s) ^ k` (`awayMapG`, Mathlib's `IsLocalization.map`), and
  `twistAwayLift : R' ⊗[R] (A_s)_n →ₗ[R'] (B_{f s})_n`, `r ⊗ m ↦ r • twistAwayMap m`.
* **`twistAwayLift_bijective`**: `(B_{f s})_n = R' ⊗_R (A_s)_n`.

## Natural-language proof (of `twistAwayLift_bijective`)

Exactly the proof of `Stacks01n2AwayBaseChange.awayLift_bijective` with the degree shifted by `n`: write
`L := twistAwayLift`, `mk_k : 𝒜_p → (A_s)_n`, `a ↦ a / s^k` (`p = k i + n`), `mk'_k` for `ℬ`, `L_p := pieceLift p :
R' ⊗ 𝒜_p → ℬ_p` (bijective by `pieceLift_bijective`).
1. Compatibility: `L ∘ (id ⊗ mk_k) = mk'_k ∘ L_p` (check on `r ⊗ a`: both give `r • (f a / (f s)^k)`).
2. Common denominators: every element of `R' ⊗_R (A_s)_n` is `(id ⊗ mk_k) t` for some `k` and
   `t ∈ R' ⊗ 𝒜_p`, `p = k i + n` (induction on the tensor; for a sum use `mk_{k₁+k₂} (s^{k₂} a) = mk_{k₁} a`;
   for the zero tensor take `k := |n|`, `p := |n| i + n ≥ 0`).
3. Surjective: `y ∈ (B_{f s})_n` is `b / (f s)^k` with `b ∈ ℬ_p`; `b = L_p t`, so `y = L ((id ⊗ mk_k) t)`.
4. Injective: if `L ((id ⊗ mk_k) t) = 0` then `mk'_k (L_p t) = 0`, so `(f s)^N · L_p t = 0` in `B` for some `N`
   (`IsLocalization.mk'_eq_zero_iff`). Multiplication by `s^N` (resp. `(f s)^N`) is compatible with `L_p`, so
   `L_{N i + p} ((id ⊗ s^N) t) = 0`, hence `(id ⊗ s^N) t = 0` by injectivity of `L_{N i + p}`, and
   `(id ⊗ mk_k) t = (id ⊗ mk_{k+N}) ((id ⊗ s^N) t) = 0`.

Edge cases: `n < 0` is allowed (the module may be `0`); `R' = 0` gives `B = 0` and both sides `0`; `s = 0` gives
zero localizations on both sides. `0 < i` is needed only to have some degree `p = k i + n ≥ 0`
(`exists_deg`) and to cancel `i` in `mkTwist_mulPowTwist`.

Source: Stacks 01N2 (last sentence, `O_{Proj B}(n) = ψ^* O_{Proj A}(n)`), via the local description
`Γ(D₊(f s), O(n)) = (B_{f s})_n` of Stacks 01M7/01MN; the paper uses this only through Stacks 01N2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

open HomogeneousLocalization Graded
open scoped TensorProduct

noncomputable section

namespace MiyaokaMori.Stacks01n2

/-! ## The degree-`n` part of `C_s` -/

section TwistAway

variable {S : Type u} [CommRing S] {C : Type u} [CommRing C] [Algebra S C] (𝒞 : ℕ → Submodule S C)
  [GradedAlgebra 𝒞] {s : C} {i : ℕ} (hs : s ∈ 𝒞 i) (hi : 0 < i) (n : ℤ)

omit [GradedAlgebra 𝒞] in
include hi in
/-- Some degree `p = k i + n ≥ 0` exists (`k := |n|`). -/
theorem exists_deg : ∃ p k : ℕ, (p : ℤ) = k * i + n := by
  have h1 : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have h2 : (0 : ℤ) ≤ (n.natAbs : ℤ) * i + n := by
    rw [Int.natCast_natAbs]
    nlinarith [abs_nonneg n, neg_le_abs n]
  refine ⟨((n.natAbs : ℤ) * i + n).toNat, n.natAbs, ?_⟩
  rw [Int.toNat_of_nonneg h2]

/-- The degree-`n` part of `C_s`: fractions `a / s ^ k` with `a ∈ 𝒞 p`, `p = k i + n`, as an `S`-submodule
of `Localization.Away s`. -/
def twistAway : Submodule S (Localization.Away s) where
  carrier := {x | ∃ (p k : ℕ) (a : C), a ∈ 𝒞 p ∧ (p : ℤ) = k * i + n ∧
    x = Localization.mk a (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)}
  zero_mem' := by
    obtain ⟨p, k, hp⟩ := exists_deg hi n
    exact ⟨p, k, 0, zero_mem _, hp, (Localization.mk_zero _).symm⟩
  add_mem' := by
    rintro x y ⟨p, k, a, ha, hp, rfl⟩ ⟨p', k', a', ha', hp', rfl⟩
    refine ⟨k * i + p', k + k', s ^ k * a' + s ^ k' * a, ?_, ?_, ?_⟩
    · refine add_mem ?_ ?_
      · simpa [smul_eq_mul] using SetLike.mul_mem_graded (SetLike.pow_mem_graded k hs) ha'
      · have := SetLike.mul_mem_graded (SetLike.pow_mem_graded k' hs) ha
        rwa [smul_eq_mul, show k' * i + p = k * i + p' by zify; linarith] at this
    · push_cast; linarith
    · rw [Localization.add_mk]
      congr 1
      exact Subtype.ext (pow_add s k k').symm
  smul_mem' := by
    rintro r x ⟨p, k, a, ha, hp, rfl⟩
    exact ⟨p, k, r • a, (𝒞 p).smul_mem r ha, hp, Localization.smul_mk r a _⟩

theorem mem_twistAway {x : Localization.Away s} :
    x ∈ twistAway 𝒞 hs hi n ↔ ∃ (p k : ℕ) (a : C), a ∈ 𝒞 p ∧ (p : ℤ) = k * i + n ∧
      x = Localization.mk a (⟨s ^ k, k, rfl⟩ : Submonoid.powers s) :=
  Iff.rfl

/-- `a ↦ a / s ^ k` on `𝒞 p`, `p = k i + n`, as an `S`-linear map into `(C_s)_n`. -/
def mkTwist (p k : ℕ) (hp : (p : ℤ) = k * i + n) : 𝒞 p →ₗ[S] twistAway 𝒞 hs hi n where
  toFun a := ⟨Localization.mk (a : C) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s), p, k, a, a.2, hp, rfl⟩
  map_add' a b := Subtype.ext (by
    change Localization.mk (a + b : C) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s) =
      Localization.mk (a : C) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s) +
        Localization.mk (b : C) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)
    rw [Localization.add_mk_self])
  map_smul' r a := Subtype.ext (by
    change Localization.mk (r • a : C) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s) =
      r • Localization.mk (a : C) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)
    rw [Localization.smul_mk])

theorem coe_mkTwist (p k : ℕ) (hp : (p : ℤ) = k * i + n) (a : 𝒞 p) :
    (mkTwist 𝒞 hs hi n p k hp a : Localization.Away s) =
      Localization.mk (a : C) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s) := rfl

theorem exists_mkTwist_eq (x : twistAway 𝒞 hs hi n) :
    ∃ (p k : ℕ) (hp : (p : ℤ) = k * i + n) (a : 𝒞 p), mkTwist 𝒞 hs hi n p k hp a = x := by
  obtain ⟨p, k, a, ha, hp, hx⟩ := x.2
  exact ⟨p, k, hp, ⟨a, ha⟩, Subtype.ext hx.symm⟩

/-- Multiplication by `s ^ N`, `𝒞 p → 𝒞 p'` for `p' = N i + p`. -/
def mulPowTwist (N : ℕ) {p p' : ℕ} (h : p' = N * i + p) : 𝒞 p →ₗ[S] 𝒞 p' where
  toFun a := ⟨s ^ N * (a : C), by
    rw [h]
    simpa [smul_eq_mul] using SetLike.mul_mem_graded (SetLike.pow_mem_graded N hs) a.2⟩
  map_add' a b := Subtype.ext (by simp [mul_add])
  map_smul' r a := Subtype.ext (by simp)

theorem coe_mulPowTwist (N : ℕ) {p p' : ℕ} (h : p' = N * i + p) (a : 𝒞 p) :
    (mulPowTwist 𝒞 hs N h a : C) = s ^ N * (a : C) := rfl

theorem mkTwist_mulPowTwist (N : ℕ) {p p' k k' : ℕ} (h : p' = N * i + p) (hp : (p : ℤ) = k * i + n)
    (hp' : (p' : ℤ) = k' * i + n) (a : 𝒞 p) :
    mkTwist 𝒞 hs hi n p' k' hp' (mulPowTwist 𝒞 hs N h a) = mkTwist 𝒞 hs hi n p k hp a := by
  have hk : k' = k + N := by
    have hi' : (i : ℤ) ≠ 0 := by exact_mod_cast hi.ne'
    have : (k' : ℤ) * i = ((k + N : ℕ) : ℤ) * i := by
      subst h
      push_cast at hp' ⊢
      linarith
    exact_mod_cast mul_right_cancel₀ hi' this
  subst hk
  apply Subtype.ext
  rw [coe_mkTwist, coe_mkTwist, coe_mulPowTwist, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [pow_add]
  ring

theorem exists_pow_mul_eq_zero_of_mkTwist_eq_zero {p k : ℕ} (hp : (p : ℤ) = k * i + n) (b : 𝒞 p)
    (h : mkTwist 𝒞 hs hi n p k hp b = 0) : ∃ N : ℕ, s ^ N * (b : C) = 0 := by
  have hv := congrArg Subtype.val h
  rw [coe_mkTwist, Submodule.coe_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hv
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := hv
  exact ⟨N, hN⟩

/-- `(C_s)_n` is stable under multiplication by the degree-zero localization `𝒞_(s)`. -/
theorem val_mul_mem (u : Away 𝒞 s) {x : Localization.Away s} (hx : x ∈ twistAway 𝒞 hs hi n) :
    u.val * x ∈ twistAway 𝒞 hs hi n := by
  obtain ⟨q, c, hc, rfl⟩ := Away.mk_surjective 𝒞 hs u
  obtain ⟨p, k, a, ha, hp, rfl⟩ := hx
  refine ⟨q * i + p, q + k, c * a, ?_, ?_, ?_⟩
  · simpa [smul_eq_mul] using SetLike.mul_mem_graded hc ha
  · push_cast; linarith
  · rw [Away.val_mk, Localization.mk_mul]
    congr 1
    exact Subtype.ext (pow_add s q k).symm

variable {T : Type u} [CommRing T] [Algebra S T]

theorem baseChange_mkTwist_mulPowTwist (N : ℕ) {p p' k k' : ℕ} (h : p' = N * i + p)
    (hp : (p : ℤ) = k * i + n) (hp' : (p' : ℤ) = k' * i + n) (α : T ⊗[S] 𝒞 p) :
    (mkTwist 𝒞 hs hi n p' k' hp').baseChange T ((mulPowTwist 𝒞 hs N h).baseChange T α) =
      (mkTwist 𝒞 hs hi n p k hp).baseChange T α := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  congr 2
  exact LinearMap.ext (mkTwist_mulPowTwist 𝒞 hs hi n N h hp hp')

/-- Common denominators: every element of `T ⊗[S] (C_s)_n` comes from some `T ⊗[S] 𝒞 p`. -/
theorem exists_baseChange_mkTwist (t : T ⊗[S] twistAway 𝒞 hs hi n) :
    ∃ (p k : ℕ) (hp : (p : ℤ) = k * i + n) (α : T ⊗[S] 𝒞 p),
      (mkTwist 𝒞 hs hi n p k hp).baseChange T α = t := by
  induction t using TensorProduct.induction_on with
  | zero =>
    obtain ⟨p, k, hp⟩ := exists_deg hi n
    exact ⟨p, k, hp, 0, map_zero _⟩
  | tmul r x =>
    obtain ⟨p, k, hp, a, rfl⟩ := exists_mkTwist_eq 𝒞 hs hi n x
    exact ⟨p, k, hp, r ⊗ₜ a, by rw [LinearMap.baseChange_tmul]⟩
  | add t₁ t₂ ih₁ ih₂ =>
    obtain ⟨p₁, k₁, hp₁, α₁, rfl⟩ := ih₁
    obtain ⟨p₂, k₂, hp₂, α₂, rfl⟩ := ih₂
    have hp : ((k₂ * i + p₁ : ℕ) : ℤ) = (k₁ + k₂ : ℕ) * i + n := by push_cast; linarith
    have h₂ : k₂ * i + p₁ = k₁ * i + p₂ := by zify; linarith
    refine ⟨k₂ * i + p₁, k₁ + k₂, hp, (mulPowTwist 𝒞 hs k₂ rfl).baseChange T α₁ +
      (mulPowTwist 𝒞 hs k₁ h₂).baseChange T α₂, ?_⟩
    rw [map_add, baseChange_mkTwist_mulPowTwist 𝒞 hs hi n k₂ rfl hp₁ hp,
      baseChange_mkTwist_mulPowTwist 𝒞 hs hi n k₁ h₂ hp₂ hp]

end TwistAway

/-! ## Base change `(B_{f s})_n = R' ⊗_R (A_s)_n` -/

section TwistAwayBaseChange

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (fR : A →ₐ[R] B) (hfR : ∀ a, fR a = f a)

omit [Algebra R R'] [IsScalarTower R R' B] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- `A_s →+* B_{f s}`, `a / s ^ k ↦ f a / (f s) ^ k` (Mathlib's `IsLocalization.map`; spelled with `f s` so
that it lands in the same `Localization.Away (f s)` as `HomogeneousLocalization.Away.map f s`). -/
def awayMapG (s : A) : Localization.Away s →+* Localization.Away (f s) :=
  IsLocalization.map (Localization.Away (f s)) (f : A →+* B)
    (show Submonoid.powers s ≤ (Submonoid.powers (f s)).comap (f : A →+* B) by
      rintro x ⟨k, rfl⟩
      exact ⟨k, (map_pow (f : A →+* B) s k).symm⟩)

omit [Algebra R R'] [IsScalarTower R R' B] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem awayMapG_mk (s a : A) (k : ℕ) :
    awayMapG 𝒜 ℬ f s (Localization.mk a (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)) =
      Localization.mk (f a) (⟨f s ^ k, k, rfl⟩ : Submonoid.powers (f s)) := by
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', awayMapG, IsLocalization.map_mk']
  congr 1
  exact Subtype.ext (map_pow (f : A →+* B) s k)

omit [Algebra R R'] [IsScalarTower R R' B] in
theorem awayMapG_val {s : A} {i : ℕ} (hs : s ∈ 𝒜 i) (u : Away 𝒜 s) :
    awayMapG 𝒜 ℬ f s u.val = (Away.map f s u).val := by
  obtain ⟨q, c, hc, rfl⟩ := Away.mk_surjective 𝒜 hs u
  rw [Away.map_mk, Away.val_mk, Away.val_mk, awayMapG_mk]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- `R → R' → B_{f s}`: not a global instance; supply it locally. -/
theorem isScalarTower_R_R'_away (s : A) : IsScalarTower R R' (Localization.Away (f s)) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change OreLocalization.numeratorRingHom (algebraMap R B r) =
      OreLocalization.numeratorRingHom (algebraMap R' B (algebraMap R R' r))
    rw [← IsScalarTower.algebraMap_apply]

attribute [local instance] isScalarTower_R_R'_away

variable {s : A} {i : ℕ} (hs : s ∈ 𝒜 i) (hi : 0 < i) (n : ℤ)

theorem awayMap_mem {x : Localization.Away s} (hx : x ∈ twistAway 𝒜 hs hi n) :
    awayMapG 𝒜 ℬ f s x ∈ twistAway ℬ (map_mem f hs) hi n := by
  obtain ⟨p, k, a, ha, hp, rfl⟩ := hx
  exact ⟨p, k, f a, map_mem f ha, hp, awayMapG_mk 𝒜 ℬ f s a k⟩

/-- `(A_s)_n →ₗ[R] (B_{f s})_n`, `a / s ^ k ↦ f a / (f s) ^ k`. -/
def twistAwayMap : twistAway 𝒜 hs hi n →ₗ[R] twistAway ℬ (map_mem f hs) hi n where
  toFun x := ⟨awayMapG 𝒜 ℬ f s x, awayMap_mem 𝒜 ℬ f hs hi n x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := by
    apply Subtype.ext
    obtain ⟨p, k, hp, a, rfl⟩ := exists_mkTwist_eq 𝒜 hs hi n x
    change awayMapG 𝒜 ℬ f s
        (r • Localization.mk (a : A) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)) =
      r • awayMapG 𝒜 ℬ f s
        (Localization.mk (a : A) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s))
    rw [Localization.smul_mk, awayMapG_mk, awayMapG_mk, Localization.smul_mk]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_algebraMap 𝒜 ℬ f fR hfR]

theorem coe_twistAwayMap (x : twistAway 𝒜 hs hi n) :
    (twistAwayMap 𝒜 ℬ f fR hfR hs hi n x : Localization.Away (f s)) =
      awayMapG 𝒜 ℬ f s x := rfl

theorem twistAwayMap_mkTwist (p k : ℕ) (hp : (p : ℤ) = k * i + n) (a : 𝒜 p) :
    twistAwayMap 𝒜 ℬ f fR hfR hs hi n (mkTwist 𝒜 hs hi n p k hp a) =
      mkTwist ℬ (map_mem f hs) hi n p k hp (pieceMap 𝒜 ℬ f fR hfR p a) :=
  Subtype.ext (awayMapG_mk 𝒜 ℬ f s a k)

/-- `R' ⊗[R] (A_s)_n → (B_{f s})_n`, `r ⊗ m ↦ r • twistAwayMap m`. -/
def twistAwayLift : R' ⊗[R] twistAway 𝒜 hs hi n →ₗ[R'] twistAway ℬ (map_mem f hs) hi n :=
  (TensorProduct.isBaseChange R (twistAway 𝒜 hs hi n) R').lift (twistAwayMap 𝒜 ℬ f fR hfR hs hi n)

theorem twistAwayLift_one_tmul (x : twistAway 𝒜 hs hi n) :
    twistAwayLift 𝒜 ℬ f fR hfR hs hi n (1 ⊗ₜ x) = twistAwayMap 𝒜 ℬ f fR hfR hs hi n x :=
  IsBaseChange.lift_eq _ _ x

theorem twistAwayLift_tmul (r : R') (x : twistAway 𝒜 hs hi n) :
    twistAwayLift 𝒜 ℬ f fR hfR hs hi n (r ⊗ₜ x) = r • twistAwayMap 𝒜 ℬ f fR hfR hs hi n x := by
  have : r ⊗ₜ[R] x = r • ((1 : R') ⊗ₜ[R] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, twistAwayLift_one_tmul]

theorem twistAwayLift_baseChange_mkTwist (p k : ℕ) (hp : (p : ℤ) = k * i + n) (α : R' ⊗[R] 𝒜 p) :
    twistAwayLift 𝒜 ℬ f fR hfR hs hi n ((mkTwist 𝒜 hs hi n p k hp).baseChange R' α) =
      mkTwist ℬ (map_mem f hs) hi n p k hp (pieceLift 𝒜 ℬ f fR hfR p α) := by
  induction α using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, twistAwayLift_tmul, pieceLift_tmul, map_smul, twistAwayMap_mkTwist]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem pieceLift_baseChange_mulPowTwist (N : ℕ) {p p' : ℕ} (h : p' = N * i + p) (α : R' ⊗[R] 𝒜 p) :
    pieceLift 𝒜 ℬ f fR hfR p' ((mulPowTwist 𝒜 hs N h).baseChange R' α) =
      mulPowTwist ℬ (map_mem f hs) N h (pieceLift 𝒜 ℬ f fR hfR p α) := by
  induction α using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, pieceLift_tmul, pieceLift_tmul, map_smul]
    congr 1
    apply Subtype.ext
    rw [pieceMap_apply, coe_mulPowTwist, coe_mulPowTwist, pieceMap_apply, map_mul, map_pow]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

variable (hbc : IsBaseChange R' fR.toLinearMap)

include hbc in
theorem twistAwayLift_injective : Function.Injective (twistAwayLift 𝒜 ℬ f fR hfR hs hi n) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨p, k, hp, α, rfl⟩ := exists_baseChange_mkTwist 𝒜 hs hi n t
  rw [twistAwayLift_baseChange_mkTwist] at ht
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_mkTwist_eq_zero ℬ (map_mem f hs) hi n hp _ ht
  have h1 : mulPowTwist ℬ (map_mem f hs) N rfl (pieceLift 𝒜 ℬ f fR hfR p α) = 0 :=
    Subtype.ext (by rw [coe_mulPowTwist]; exact hN)
  rw [← pieceLift_baseChange_mulPowTwist 𝒜 ℬ f fR hfR hs] at h1
  have h2 := pieceLift_injective 𝒜 ℬ f fR hfR hbc (N * i + p) (h1.trans (map_zero _).symm)
  have hp' : ((N * i + p : ℕ) : ℤ) = (k + N : ℕ) * i + n := by push_cast; linarith
  rw [← baseChange_mkTwist_mulPowTwist 𝒜 hs hi n N rfl hp hp' α, h2, map_zero]

include hbc in
theorem twistAwayLift_surjective : Function.Surjective (twistAwayLift 𝒜 ℬ f fR hfR hs hi n) := by
  intro y
  obtain ⟨p, k, hp, b, rfl⟩ := exists_mkTwist_eq ℬ (map_mem f hs) hi n y
  obtain ⟨α, hα⟩ := pieceLift_surjective 𝒜 ℬ f fR hfR hbc p b
  exact ⟨(mkTwist 𝒜 hs hi n p k hp).baseChange R' α, by
    rw [twistAwayLift_baseChange_mkTwist, hα]⟩

include hbc in
/-- **Stacks 01N2, chart-level algebra for `O(n)`**: `(B_{f s})_n = R' ⊗_R (A_s)_n`. -/
theorem twistAwayLift_bijective : Function.Bijective (twistAwayLift 𝒜 ℬ f fR hfR hs hi n) :=
  ⟨twistAwayLift_injective 𝒜 ℬ f fR hfR hs hi n hbc, twistAwayLift_surjective 𝒜 ℬ f fR hfR hs hi n hbc⟩

/-- The `𝒜_(s)`-action is compatible with `twistAwayLift` on pure tensors: multiplying
`twistAwayLift (r ⊗ m)` by `r₀ • Away.map f s u` gives `twistAwayLift ((r₀ r) ⊗ (u • m))`. -/
theorem val_smul_map_mul_twistAwayLift_tmul (r₀ r : R') (u : Away 𝒜 s) (m : twistAway 𝒜 hs hi n) :
    (r₀ • Away.map f s u).val *
        (twistAwayLift 𝒜 ℬ f fR hfR hs hi n (r ⊗ₜ m) : Localization.Away (f s)) =
      twistAwayLift 𝒜 ℬ f fR hfR hs hi n ((r₀ * r) ⊗ₜ ⟨u.val * m, val_mul_mem 𝒜 hs hi n u m.2⟩) := by
  rw [twistAwayLift_tmul, twistAwayLift_tmul, HomogeneousLocalization.val_smul, Submodule.coe_smul,
    Submodule.coe_smul, smul_mul_smul_comm]
  congr 1
  have h1 : (twistAwayMap 𝒜 ℬ f fR hfR hs hi n ⟨u.val * m, val_mul_mem 𝒜 hs hi n u m.2⟩ :
      Localization.Away (f s)) = awayMapG 𝒜 ℬ f s (u.val * m) := rfl
  have h2 : (twistAwayMap 𝒜 ℬ f fR hfR hs hi n m : Localization.Away (f s)) =
      awayMapG 𝒜 ℬ f s m := rfl
  rw [h1, h2, map_mul, awayMapG_val 𝒜 ℬ f hs]

end TwistAwayBaseChange

end MiyaokaMori.Stacks01n2

end
