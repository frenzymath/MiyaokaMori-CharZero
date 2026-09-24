import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01n2TwistStalkSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensor

/-! # Stacks 01N2 for the twisting sheaves on a fixed chart

**Stacks 01N2 (last sentence) on stalks, on a fixed chart.** Setting as in `Stacks01n2TwistStalk`
(`B = R' ⊗_R A` graded, `ρ := Proj.map f hf`, `θ := Proj.twistPullbackHom f hf n`, `M := O_{Proj 𝒜}(n)`,
`N := O_{Proj ℬ}(n)`), plus a chart: `s ∈ 𝒜 i`, `0 < i`, `y ∈ D₊(f s) = ρ⁻¹ D₊(s)`, `x := ρ y ∈ D₊(s)`.
Write `Θ := θ_y ∘ T : O_{B,y} ⊗_{O_{A,x}} M_x → N_y` for the stalk map of `θ` composed with the pullback-stalk
tensor map `T` (`AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap`).

Main result: **`twistPullbackHom_stalkMap_comp_tensorMap_bijective_of_mem_basicOpen`**: `Θ` is bijective.
Ingredients (`Stacks01n2TwistStalkAlgebra`, `Stacks01n2TwistStalkSections`):
`(A_s)_n = twistAway 𝒜 hs hi n`, `T₁ := twistAwayLift : R' ⊗_R (A_s)_n ≅ (B_{f s})_n` (`twistAwayLift_bijective`),
`secA := twistSection 𝒜 : (A_s)_n → Γ(D₊(s), M)`, `secB := twistSection ℬ : (B_{f s})_n → Γ(D₊(f s), N)`.

## Natural-language proof

* `constGerm : R' → O_{B,y}`, `r ↦ germ_y (awayToSection (r / 1))`; `jHom : R' ⊗_R (A_s)_n → O_{B,y} ⊗ M_x`,
  `r ⊗ m ↦ constGerm r • (1 ⊗ germ_x (secA m))` (well defined: `1 ⊗ germ (secA (r₀ • m)) = constGerm r₀ • (1 ⊗ germ (secA m))`
  by `one_tmul_germ_twistSection_mul`, which moves a scalar `u ∈ 𝒜_(s)` across the tensor: `1 ⊗ (germ u • μ) =
  ρ_y (germ u) ⊗ μ` and `ρ_y (germ u) = germ (Away.map f s u)` (`stalkMap_germ_awayToSection`)).
* (N2) `Θ (jHom ζ) = germ_y (secB (T₁ ζ))` (`stalkMap_tensorMap_jHom`): on `r ⊗ m`, `Θ (r • (1 ⊗ germ (secA m)))
  = constGerm r • θ_y (u_y (germ (secA m))) = constGerm r • germ (φ (secA m))` (`moduleStalkMap_transpose_unit_germ`),
  and pointwise `(r / 1) · φ (secA m) = secB (r • twistAwayMap m)` (`φ` acts by `a / s^k ↦ f a / (f s)^k`).
* (N4) `exists_twistAwayLift_eq_mul_and_jHom_eq_smul`: for `u ∈ ℬ_(f s)` and `ζ`, there is `ζ'` with
  `T₁ ζ' = u • T₁ ζ` and `jHom ζ' = germ u • jHom ζ` (write `u = Σ r_l • Away.map f s (q_l)`, `awayLift_surjective`;
  on `r ⊗ m` take `ζ' := (r_l r) ⊗ (q_l • m)`).
* (N1) `exists_unit_smul_eq_jHom`: for every `ξ ∈ O_{B,y} ⊗ M_x` there are `τ ∈ ℬ_(f s)` with `germ τ` a unit and
  `ζ` with `germ τ • ξ = jHom ζ` (tensor induction; on `b ⊗ μ` write `μ = v • germ (secA m)`
  (`exists_smul_germ_twistSection_eq`), `b ⊗ μ = (v • b) ⊗ germ (secA m)`, `germ τ · (v • b) = germ σ`
  (`exists_unit_germ_mul_eq_germ_awayToSection`), so `germ τ • (b ⊗ μ) = germ σ • jHom (1 ⊗ m)`, and (N4)).
* Injective: `Θ ξ = 0`; (N1) gives `germ τ • ξ = jHom ζ`, so `germ_y (secB (T₁ ζ)) = Θ (jHom ζ) = 0` (N2); hence
  `u • T₁ ζ = 0` with `germ u` a unit (`exists_unit_mul_eq_zero_of_germ_eq_zero`); (N4) gives `ζ'` with
  `T₁ ζ' = u • T₁ ζ = 0`, so `ζ' = 0` (`twistAwayLift_injective`) and `germ u • jHom ζ = jHom ζ' = 0`, so
  `jHom ζ = 0`, `germ τ • ξ = 0`, `ξ = 0`.
* Surjective: `ν ∈ N_y` is `v • germ (secB m')` (`exists_smul_germ_twistSection_eq` for `ℬ`), `m' = T₁ ζ`
  (`twistAwayLift_surjective`), so `ν = v • Θ (jHom ζ) = Θ (v • jHom ζ)` by (N2).

Source: Stacks 01N2 (last sentence) via 01MX; the paper uses it only through Stacks 01N2/01NO.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace HomogeneousLocalization Graded
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MiyaokaMori MiyaokaMori.WeightedJets.ProjTwisting MiyaokaMori.Stacks01n2
open scoped TensorProduct AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.Stacks01n2TwistStalk

/-- Every point of `Proj 𝒜` lies in some `D₊(s)` with `s` homogeneous of positive degree
(the prime is relevant: `ProjectiveSpectrum.not_irrelevant_le`). -/
theorem exists_mem_basicOpen {S : Type u} [CommRing S] {C : Type u} [CommRing C] [Algebra S C]
    (𝒞 : ℕ → Submodule S C) [GradedAlgebra 𝒞] (x : Proj 𝒞) :
    ∃ (i : ℕ) (s : C), s ∈ 𝒞 i ∧ 0 < i ∧ x ∈ Proj.basicOpen 𝒞 s := by
  obtain ⟨a, ha, hax⟩ := Set.not_subset.mp x.not_irrelevant_le
  have hnot : ¬ ∀ i, (DirectSum.decompose 𝒞 a i : C) ∈ x.asHomogeneousIdeal.toIdeal :=
    fun hall ↦ hax ((x.asHomogeneousIdeal.isHomogeneous.mem_iff).mpr hall)
  simp only [not_forall] at hnot
  obtain ⟨i, hi⟩ := hnot
  refine ⟨i, DirectSum.decompose 𝒞 a i, (DirectSum.decompose 𝒞 a i).2, ?_, hi⟩
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exfalso
    apply hi
    have h0 : (DirectSum.decompose 𝒞 a 0 : C) = 0 := by
      have := (HomogeneousIdeal.mem_irrelevant_iff 𝒞 a).mp ha
      rwa [GradedRing.proj_apply] at this
    rw [h0]
    exact zero_mem _
  · exact hpos

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
  (fR : A →ₐ[R] B) (hfR : ∀ a, fR a = f a)
  {s : A} {i : ℕ} (hs : s ∈ 𝒜 i) (hi : 0 < i) (n : ℤ) (y : Proj ℬ) (hy : y ∈ Proj.basicOpen ℬ (f s))

attribute [local instance] AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra
attribute [local instance] awayAlgebra awayAlgebraBR awayAlgebraAB isScalarTower_R_R'

/-- Moving a scalar `u ∈ 𝒜_(s)` across the tensor `O_{B,y} ⊗_{O_{A,x}} M_x`:
`1 ⊗ germ (twistSection (u • m)) = germ (awayToSection (Away.map f s u)) • (1 ⊗ germ (twistSection m))`. -/
theorem one_tmul_germ_twistSection_mul (u : Away 𝒜 s) (m : twistAway 𝒜 hs hi n) :
    (1 : (Proj ℬ).presheaf.stalk y) ⊗ₜ[(Proj 𝒜).presheaf.stalk ((Proj.map f hf).base y)]
        (Proj.twist 𝒜 n).presheaf.germ (Proj.basicOpen 𝒜 s) ((Proj.map f hf).base y) hy
          (twistSection 𝒜 hs hi n ⟨u.val * m, val_mul_mem 𝒜 hs hi n u m.2⟩) =
      (Proj ℬ).presheaf.germ (Proj.basicOpen ℬ (f s)) y hy (Proj.awayToSection ℬ (f s) (Away.map f s u)) •
        ((1 : (Proj ℬ).presheaf.stalk y) ⊗ₜ[(Proj 𝒜).presheaf.stalk ((Proj.map f hf).base y)]
          (Proj.twist 𝒜 n).presheaf.germ (Proj.basicOpen 𝒜 s) ((Proj.map f hf).base y) hy
            (twistSection 𝒜 hs hi n m)) := by
  rw [← germ_awayToSection_smul_germ_twistSection 𝒜 hs hi n (x := (Proj.map f hf).base y) hy u m,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]
  congr 1
  exact stalkMap_germ_awayToSection 𝒜 ℬ f hf hs y hy u

/-- `(A_s)_n → O_{B,y} ⊗_{O_{A,x}} M_x`, `m ↦ 1 ⊗ germ (twistSection m)`. -/
def oneTmulGerm : twistAway 𝒜 hs hi n →+ modulePullbackStalkTensor (Proj.map f hf) (Proj.twist 𝒜 n) y where
  toFun m := (1 : (Proj ℬ).presheaf.stalk y) ⊗ₜ[(Proj 𝒜).presheaf.stalk ((Proj.map f hf).base y)]
    (Proj.twist 𝒜 n).presheaf.germ (Proj.basicOpen 𝒜 s) ((Proj.map f hf).base y) hy (twistSection 𝒜 hs hi n m)
  map_zero' := by rw [twistSection_zero, map_zero, TensorProduct.tmul_zero]
  map_add' m m' := by rw [twistSection_add, map_add, TensorProduct.tmul_add]

theorem oneTmulGerm_apply (m : twistAway 𝒜 hs hi n) :
    oneTmulGerm 𝒜 ℬ f hf hs hi n y hy m =
      (1 : (Proj ℬ).presheaf.stalk y) ⊗ₜ[(Proj 𝒜).presheaf.stalk ((Proj.map f hf).base y)]
        (Proj.twist 𝒜 n).presheaf.germ (Proj.basicOpen 𝒜 s) ((Proj.map f hf).base y) hy
          (twistSection 𝒜 hs hi n m) := rfl

/-- `R' → (A_s)_n → O_{B,y} ⊗_{O_{A,x}} M_x`, `r ↦ m ↦ constGerm r • (1 ⊗ germ (twistSection m))`. -/
def jBil : R' →+ twistAway 𝒜 hs hi n →+ modulePullbackStalkTensor (Proj.map f hf) (Proj.twist 𝒜 n) y where
  toFun r := (DistribSMul.toAddMonoidHom _ (constGerm ℬ hy r)).comp (oneTmulGerm 𝒜 ℬ f hf hs hi n y hy)
  map_zero' := AddMonoidHom.ext fun m ↦ by
    change constGerm ℬ hy 0 • oneTmulGerm 𝒜 ℬ f hf hs hi n y hy m = 0
    rw [map_zero, zero_smul]
  map_add' r r' := AddMonoidHom.ext fun m ↦ by
    change constGerm ℬ hy (r + r') • oneTmulGerm 𝒜 ℬ f hf hs hi n y hy m =
      constGerm ℬ hy r • oneTmulGerm 𝒜 ℬ f hf hs hi n y hy m +
        constGerm ℬ hy r' • oneTmulGerm 𝒜 ℬ f hf hs hi n y hy m
    rw [map_add, add_smul]

theorem jBil_apply (r : R') (m : twistAway 𝒜 hs hi n) :
    jBil 𝒜 ℬ f hf hs hi n y hy r m = constGerm ℬ hy r • oneTmulGerm 𝒜 ℬ f hf hs hi n y hy m := rfl

include fR hfR in
/-- `jBil` is `R`-balanced: `1 ⊗ germ (twistSection (r₀ • m)) = constGerm r₀ • (1 ⊗ germ (twistSection m))`. -/
theorem jBil_smul (r₀ : R) (r : R') (m : twistAway 𝒜 hs hi n) :
    jBil 𝒜 ℬ f hf hs hi n y hy (r₀ • r) m = jBil 𝒜 ℬ f hf hs hi n y hy r (r₀ • m) := by
  rw [jBil_apply, jBil_apply, oneTmulGerm_apply, oneTmulGerm_apply]
  have h1 : (r₀ • m : twistAway 𝒜 hs hi n) =
      ⟨(awayAlgebraMap 𝒜 s r₀).val * m, val_mul_mem 𝒜 hs hi n _ m.2⟩ := by
    apply Subtype.ext
    change r₀ • (m : Localization.Away s) = (awayAlgebraMap 𝒜 s r₀).val * (m : Localization.Away s)
    rw [val_awayAlgebraMap, Algebra.smul_def]
    rfl
  rw [h1, one_tmul_germ_twistSection_mul 𝒜 ℬ f hf hs hi n y hy, awayMap_awayAlgebraMap 𝒜 ℬ f fR hfR,
    ← constGerm_apply, Algebra.smul_def, map_mul, mul_smul, smul_comm]

/-- `R' ⊗_R (A_s)_n → O_{B,y} ⊗_{O_{A,x}} M_x`, `r ⊗ m ↦ constGerm r • (1 ⊗ germ (twistSection m))`. -/
def jHom : R' ⊗[R] twistAway 𝒜 hs hi n →+ modulePullbackStalkTensor (Proj.map f hf) (Proj.twist 𝒜 n) y :=
  TensorProduct.liftAddHom (jBil 𝒜 ℬ f hf hs hi n y hy) (jBil_smul 𝒜 ℬ f hf fR hfR hs hi n y hy)

theorem jHom_tmul (r : R') (m : twistAway 𝒜 hs hi n) :
    jHom 𝒜 ℬ f hf fR hfR hs hi n y hy (r ⊗ₜ m) =
      constGerm ℬ hy r •
        ((1 : (Proj ℬ).presheaf.stalk y) ⊗ₜ[(Proj 𝒜).presheaf.stalk ((Proj.map f hf).base y)]
          (Proj.twist 𝒜 n).presheaf.germ (Proj.basicOpen 𝒜 s) ((Proj.map f hf).base y) hy
            (twistSection 𝒜 hs hi n m)) := rfl

/-- (N2) `Θ (jHom ζ) = germ_y (twistSection (twistAwayLift ζ))`. -/
theorem stalkMap_tensorMap_jHom (ζ : R' ⊗[R] twistAway 𝒜 hs hi n) :
    moduleStalkMap (Proj ℬ) y (Proj.twistPullbackHom f hf n)
        (modulePullbackStalkTensorMap (Proj.map f hf) (Proj.twist 𝒜 n) y
          (jHom 𝒜 ℬ f hf fR hfR hs hi n y hy ζ)) =
      (Proj.twist ℬ n).presheaf.germ (Proj.basicOpen ℬ (f s)) y hy
        (twistSection ℬ (map_mem f hs) hi n (twistAwayLift 𝒜 ℬ f fR hfR hs hi n ζ)) := by
  have key : ∀ m : twistAway 𝒜 hs hi n,
      moduleStalkMap (Proj ℬ) y (Proj.twistPullbackHom f hf n)
        (modulePullbackStalkUnit (Proj.map f hf) (Proj.twist 𝒜 n) y
          ((Proj.twist 𝒜 n).presheaf.germ (Proj.basicOpen 𝒜 s) ((Proj.map f hf).base y) hy
            (twistSection 𝒜 hs hi n m))) =
      (Proj.twist ℬ n).presheaf.germ ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 s) y hy
        ((Proj.twistToPushforward f hf n).app (Proj.basicOpen 𝒜 s) (twistSection 𝒜 hs hi n m)) :=
    fun m ↦ MiyaokaMori.RelativeProjTwistLocalIso.moduleStalkMap_transpose_unit_germ (Proj.map f hf)
      (Proj.twist 𝒜 n) (Proj.twist ℬ n) (Proj.twistToPushforward f hf n) y (Proj.basicOpen 𝒜 s) hy
      (twistSection 𝒜 hs hi n m)
  induction ζ using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, twistSection_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, twistSection_add, map_add, ha, hb]
  | tmul r m =>
    rw [jHom_tmul, _root_.map_smul, _root_.map_smul, modulePullbackStalkTensorMap_tmul, one_smul, key,
      twistAwayLift_tmul, constGerm_apply]
    erw [← germ_smul']
    congr 1
    obtain ⟨p, k, hp, a, rfl⟩ := exists_mkTwist_eq 𝒜 hs hi n m
    apply Subtype.ext
    funext z
    have hz := z.2
    have := z.1.isPrime
    have := (ProjectiveSpectrum.comap f hf z.1).isPrime
    change ((Proj.awayToSection ℬ (f s) (awayAlgebraMap ℬ (f s) r) :
        (ProjectiveSpectrum.Proj.structureSheaf ℬ).1.obj (op (Proj.basicOpen ℬ (f s)))).1 z).val *
        Localization.localRingHom (ProjectiveSpectrum.comap f hf z.1).asHomogeneousIdeal.toIdeal
          z.1.asHomogeneousIdeal.toIdeal (f : A →+* B) rfl
          (toFiber 𝒜 ⟨ProjectiveSpectrum.comap f hf z.1, hz⟩
            (Localization.mk (a : A) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s))) =
      toFiber ℬ z (r • twistAwayMap 𝒜 ℬ f fR hfR hs hi n (mkTwist 𝒜 hs hi n p k hp a) :
        Localization.Away (f s))
    rw [val_awayToSection_apply, val_awayAlgebraMap, IsLocalization.map_eq, RingHom.id_apply, toFiber_mk,
      Localization.localRingHom_mk, twistAwayMap_mkTwist, coe_mkTwist, Localization.smul_mk, toFiber_mk,
      ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff]
    apply Localization.r_of_eq
    simp only [pieceMap_apply, one_mul, map_pow, GradedRingHom.toRingHom_eq_toRingHom,
      GradedRingHom.coe_toRingHom]
    rw [Algebra.smul_def]

/-- (N4) For `u ∈ ℬ_(f s)` and `ζ ∈ R' ⊗_R (A_s)_n` there is `ζ'` with `T₁ ζ' = u • T₁ ζ` and
`jHom ζ' = germ u • jHom ζ`. -/
theorem exists_twistAwayLift_eq_mul_and_jHom_eq_smul (hbc : IsBaseChange R' fR.toLinearMap)
    (u : Away ℬ (f s)) (ζ : R' ⊗[R] twistAway 𝒜 hs hi n) :
    ∃ ζ' : R' ⊗[R] twistAway 𝒜 hs hi n,
      (twistAwayLift 𝒜 ℬ f fR hfR hs hi n ζ' : Localization.Away (f s)) =
          u.val * (twistAwayLift 𝒜 ℬ f fR hfR hs hi n ζ : Localization.Away (f s)) ∧
        jHom 𝒜 ℬ f hf fR hfR hs hi n y hy ζ' =
          (Proj ℬ).presheaf.germ (Proj.basicOpen ℬ (f s)) y hy (Proj.awayToSection ℬ (f s) u) •
            jHom 𝒜 ℬ f hf fR hfR hs hi n y hy ζ := by
  obtain ⟨τ, rfl⟩ := awayLift_surjective 𝒜 ℬ f fR hfR hbc hs u
  induction τ using TensorProduct.induction_on generalizing ζ with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · rw [map_zero, map_zero, Submodule.coe_zero, HomogeneousLocalization.val_zero, zero_mul]
    · rw [map_zero, map_zero, map_zero, map_zero, zero_smul]
  | add τ₁ τ₂ ih₁ ih₂ =>
    obtain ⟨ζ₁, hT₁, hj₁⟩ := ih₁ ζ
    obtain ⟨ζ₂, hT₂, hj₂⟩ := ih₂ ζ
    refine ⟨ζ₁ + ζ₂, ?_, ?_⟩
    · rw [map_add, map_add, Submodule.coe_add, hT₁, hT₂, HomogeneousLocalization.val_add, add_mul]
    · rw [map_add, map_add, map_add, map_add, add_smul, hj₁, hj₂]
  | tmul r₀ q =>
    induction ζ using TensorProduct.induction_on with
    | zero =>
      refine ⟨0, ?_, ?_⟩
      · rw [map_zero, Submodule.coe_zero, mul_zero]
      · rw [map_zero, smul_zero]
    | add ζ₁ ζ₂ ih₁ ih₂ =>
      obtain ⟨ζ₁', hT₁, hj₁⟩ := ih₁
      obtain ⟨ζ₂', hT₂, hj₂⟩ := ih₂
      refine ⟨ζ₁' + ζ₂', ?_, ?_⟩
      · rw [map_add, map_add, Submodule.coe_add, Submodule.coe_add, hT₁, hT₂, mul_add]
      · rw [map_add, map_add, hj₁, hj₂, smul_add]
    | tmul r m =>
      refine ⟨(r₀ * r) ⊗ₜ ⟨q.val * m, val_mul_mem 𝒜 hs hi n q m.2⟩, ?_, ?_⟩
      · rw [awayLift_tmul]
        exact (val_smul_map_mul_twistAwayLift_tmul 𝒜 ℬ f fR hfR hs hi n r₀ r q m).symm
      · rw [jHom_tmul, jHom_tmul, one_tmul_germ_twistSection_mul 𝒜 ℬ f hf hs hi n y hy, awayLift_tmul]
        erw [germ_awayToSection_smul ℬ hy]
        rw [map_mul]
        simp only [smul_smul]
        congr 1
        ring

/-- (N1) Every `ξ ∈ O_{B,y} ⊗_{O_{A,x}} M_x` becomes an element of the image of `jHom` after multiplication
by the germ of some `τ ∈ ℬ_(f s)` which is a unit at `y`. -/
theorem exists_unit_smul_eq_jHom (hbc : IsBaseChange R' fR.toLinearMap)
    (ξ : modulePullbackStalkTensor (Proj.map f hf) (Proj.twist 𝒜 n) y) :
    ∃ τ : Away ℬ (f s),
      IsUnit ((Proj ℬ).presheaf.germ (Proj.basicOpen ℬ (f s)) y hy (Proj.awayToSection ℬ (f s) τ)) ∧
      ∃ ζ : R' ⊗[R] twistAway 𝒜 hs hi n,
        (Proj ℬ).presheaf.germ (Proj.basicOpen ℬ (f s)) y hy (Proj.awayToSection ℬ (f s) τ) • ξ =
          jHom 𝒜 ℬ f hf fR hfR hs hi n y hy ζ := by
  induction ξ using TensorProduct.induction_on with
  | zero => exact ⟨1, by rw [map_one, map_one]; exact isUnit_one, 0, by rw [smul_zero, map_zero]⟩
  | add ξ₁ ξ₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h₁, ζ₁, e₁⟩ := ih₁
    obtain ⟨τ₂, h₂, ζ₂, e₂⟩ := ih₂
    obtain ⟨ζ₁', -, hj₁⟩ := exists_twistAwayLift_eq_mul_and_jHom_eq_smul 𝒜 ℬ f hf fR hfR hs hi n y hy hbc τ₂ ζ₁
    obtain ⟨ζ₂', -, hj₂⟩ := exists_twistAwayLift_eq_mul_and_jHom_eq_smul 𝒜 ℬ f hf fR hfR hs hi n y hy hbc τ₁ ζ₂
    refine ⟨τ₁ * τ₂, by rw [map_mul, map_mul]; exact h₁.mul h₂, ζ₁' + ζ₂', ?_⟩
    rw [map_mul, map_mul, smul_add, map_add, mul_smul, mul_smul, e₂, ← hj₂, smul_comm, e₁, ← hj₁]
  | tmul b μ =>
    obtain ⟨v, m, rfl⟩ := exists_smul_germ_twistSection_eq 𝒜 hs hi n (x := (Proj.map f hf).base y) hy μ
    obtain ⟨τ, σ, hτ, hτσ⟩ := exists_unit_germ_mul_eq_germ_awayToSection ℬ (map_mem f hs) hi hy (v • b)
    obtain ⟨ζ', -, hj⟩ := exists_twistAwayLift_eq_mul_and_jHom_eq_smul 𝒜 ℬ f hf fR hfR hs hi n y hy hbc σ
      (1 ⊗ₜ m)
    refine ⟨τ, hτ, ζ', ?_⟩
    rw [hj, jHom_tmul, map_one, one_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', smul_eq_mul, hτσ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include fR hfR hs hi hy in
/-- **Stacks 01N2 (last sentence) on stalks, on a chart**: for `y ∈ D₊(f s)`, `Θ = θ_y ∘ T` is bijective. -/
theorem twistPullbackHom_stalkMap_comp_tensorMap_bijective_of_mem_basicOpen
    (hbc : IsBaseChange R' fR.toLinearMap) :
    Function.Bijective
      (⇑(moduleStalkMap (Proj ℬ) y (Proj.twistPullbackHom f hf n)) ∘
        ⇑(modulePullbackStalkTensorMap (Proj.map f hf) (Proj.twist 𝒜 n) y)) := by
  set Θ := (moduleStalkMap (Proj ℬ) y (Proj.twistPullbackHom f hf n)).comp
    (modulePullbackStalkTensorMap (Proj.map f hf) (Proj.twist 𝒜 n) y) with hΘ
  change Function.Bijective Θ
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ξ hξ
    obtain ⟨τ, hτ, ζ, hζ⟩ := exists_unit_smul_eq_jHom 𝒜 ℬ f hf fR hfR hs hi n y hy hbc ξ
    have h1 : (Proj.twist ℬ n).presheaf.germ (Proj.basicOpen ℬ (f s)) y hy
        (twistSection ℬ (map_mem f hs) hi n (twistAwayLift 𝒜 ℬ f fR hfR hs hi n ζ)) = 0 := by
      rw [← stalkMap_tensorMap_jHom, ← hζ]
      change Θ (_ • ξ) = 0
      rw [_root_.map_smul, hξ, smul_zero]
    obtain ⟨u, hu, hu0⟩ := exists_unit_mul_eq_zero_of_germ_eq_zero ℬ (map_mem f hs) hi n hy _ h1
    obtain ⟨ζ', hT, hj⟩ := exists_twistAwayLift_eq_mul_and_jHom_eq_smul 𝒜 ℬ f hf fR hfR hs hi n y hy hbc u ζ
    have hζ' : ζ' = 0 := by
      apply twistAwayLift_injective 𝒜 ℬ f fR hfR hs hi n hbc
      rw [map_zero]
      exact Subtype.ext (hT.trans hu0)
    rw [hζ', map_zero] at hj
    have h2 : jHom 𝒜 ℬ f hf fR hfR hs hi n y hy ζ = 0 :=
      hu.smul_left_cancel.mp (hj.symm.trans (smul_zero _).symm)
    rw [h2] at hζ
    exact hτ.smul_left_cancel.mp (hζ.trans (smul_zero _).symm)
  · intro ν
    obtain ⟨v, m', rfl⟩ := exists_smul_germ_twistSection_eq ℬ (map_mem f hs) hi n hy ν
    obtain ⟨ζ, rfl⟩ := twistAwayLift_surjective 𝒜 ℬ f fR hfR hs hi n hbc m'
    refine ⟨v • jHom 𝒜 ℬ f hf fR hfR hs hi n y hy ζ, ?_⟩
    rw [_root_.map_smul]
    exact congrArg (v • ·) (stalkMap_tensorMap_jHom 𝒜 ℬ f hf fR hfR hs hi n y hy ζ)

end MiyaokaMori.Stacks01n2TwistStalk

end
