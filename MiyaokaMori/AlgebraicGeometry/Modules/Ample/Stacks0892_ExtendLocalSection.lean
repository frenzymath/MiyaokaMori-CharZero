import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01pw

/-! # Extending a local section with control of its nonvanishing locus (Stacks 01PW(2))

Let `X` be quasi-compact and quasi-separated, `N` a line bundle, `τ ∈ Γ(X, N)`, `U := X_τ`, `F` a
line bundle, `s ∈ Γ(U, F)`, and `W ⊆ U` the nonvanishing locus of `s` inside `U` (described
pointwise by germs). Then there are `e` and `σ ∈ Γ(X, F ⊗ N^{⊗e})` with `X_σ ⊓ X_τ = W`.

References: Stacks 0892, second paragraph of the proof ("By Properties, Lemma 01PW part (2) ...
`s' ∈ Γ(X, L^{⊗n} ⊗ f^*M^{⊗em})` restricting to `s ⊗ (f^*t)^{⊗e}` on `X_{f^*t}`"); Stacks 01PW;
Stacks 01CB (stalks of tensor products).

Proof sketch:
1. Stacks 01PW(2) (`Scheme.Modules.exists_tensorPow_section_restrict_eq`; line bundles are
   quasi-coherent by `IsLineBundle.isQuasicoherent`): there are `e` and `σ ∈ Γ(X, F ⊗ N^{⊗e})` with
   `σ|_U = s ⊗ (τ^{⊗e})|_U`.
2. For `y ∈ U`: `σ_y = (s ⊗ τ^{⊗e}|_U)_y` (`TopCat.Presheaf.germ_res_apply`).
3. **Germs of tensors of local sections** (`germ_moduleTensorSection_mem_maximalIdeal_smul_iff`, the
   open-set version of `mem_nonvanishingLocus_sectionTensor`):
   `(a ⊗ b)_y ∈ 𝔪_y (L ⊗ N)_y ⟺ a_y ∈ 𝔪_y L_y ∨ b_y ∈ 𝔪_y N_y`.
4. `y ∈ X_τ = X_{τ^{⊗e}}` (`nonvanishingLocus_tensorPowSection_succ` for `e ≥ 1`,
   `nonvanishingLocus_tensorPowSection_zero` for `e = 0`), so `(τ^{⊗e})_y ∉ 𝔪_y`, hence
   `y ∈ X_σ ⟺ s_y ∉ 𝔪_y F_y ⟺ y ∈ W` (hypothesis `hW`).
5. `X_σ ⊓ X_τ = W`: both sides lie in `X_τ`; pointwise by step 4, `Opens.ext`.

Edge cases: `X` empty: `U = ⊥`, `W = ⊥`, both sides are `⊥`. `W = ⊥` (`s` vanishes everywhere on `U`):
the conclusion `X_σ ⊓ X_τ = ⊥` agrees with `σ|_U = s ⊗ τ^e` vanishing everywhere. `τ = 0`: `U = ⊥`,
`s` is a section over the empty set, `W = ⊥`, and the conclusion reads `X_σ ⊓ ⊥ = ⊥`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The open-set version of `IsFrame.germ_mem_maximalIdeal_smul_iff_coord`: for a frame `(W, e)` at `y`
(`W ≤ U`), the germ of `s ∈ Γ(L, U)` lies in `𝔪_y L_y` iff the germ of the coordinate of `s|_W` lies
in `𝔪_y`. -/
theorem IsFrame.germ_mem_maximalIdeal_smul_iff_coord_res {L : X.Modules} {U W : X.Opens} {e : Γ(L, W)}
    (hf : IsFrame L W e) (hWU : W ≤ U) {y : X} (hy : y ∈ W) (s : Γ(L, U)) :
    (L.presheaf.germ U y (hWU hy) s : L.presheaf.stalk y) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (L.presheaf.stalk y)) ↔
      X.presheaf.germ W y hy (hf.coord le_rfl (L.res hWU s)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  have h := hf.coord_smul_frame le_rfl (L.res hWU s)
  rw [res_self] at h
  have hs : (L.presheaf.germ U y (hWU hy) s : L.presheaf.stalk y) =
      hf.stalkEquiv hy (X.presheaf.germ W y hy (hf.coord le_rfl (L.res hWU s))) := by
    rw [IsFrame.stalkEquiv_apply, ← germ_smul', h]
    exact (TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hWU) y hy s).symm
  refine Iff.trans (mem_maximalIdeal_smul_top_iff_of_linearEquiv (hf.stalkEquiv hy).symm _) ?_
  rw [hs, LinearEquiv.symm_apply_apply]

/-- **When the germ of a tensor of local sections lies in `𝔪_y` times the stalk** (the open-set
version of `mem_nonvanishingLocus_sectionTensor`): for line bundles `L`, `N`, `a ∈ Γ(L, U)`,
`b ∈ Γ(N, U)` and `y ∈ U`, `(a ⊗ b)_y ∈ 𝔪_y (L ⊗ N)_y ⟺ a_y ∈ 𝔪_y L_y ∨ b_y ∈ 𝔪_y N_y`.
Proof: take frames at `y`, restrict to `W₁ ⊓ W₂ ⊓ U`, write `a = α·e`, `b = β·f`,
`a ⊗ b = (αβ)·(e ⊗ f)`, and reduce through `tensorStalkEquivOfFrames` (which sends `(e⊗f)_y` to `1`)
to `α_y β_y ∈ 𝔪_y ⟺ α_y ∈ 𝔪_y ∨ β_y ∈ 𝔪_y`. -/
theorem germ_moduleTensorSection_mem_maximalIdeal_smul_iff (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle]
    {U : X.Opens} (a : Γ(L, U)) (b : Γ(N, U)) {y : X} (hy : y ∈ U) :
    ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ U y hy (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) :
        (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y)) ↔
      ((L.presheaf.germ U y hy a : L.presheaf.stalk y) ∈
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
            (⊤ : Submodule (X.presheaf.stalk y) (L.presheaf.stalk y)) ∨
        (N.presheaf.germ U y hy b : N.presheaf.stalk y) ∈
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
            (⊤ : Submodule (X.presheaf.stalk y) (N.presheaf.stalk y))) := by
  obtain ⟨W₁, hy₁, e₁, he₁⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame L y
  obtain ⟨W₂, hy₂, f₂, hf₂⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame N y
  set W : X.Opens := W₁ ⊓ W₂ ⊓ U with hWdef
  have hyW : y ∈ W := ⟨⟨hy₁, hy₂⟩, hy⟩
  have hWU : W ≤ U := inf_le_right
  have hW₁ : W ≤ W₁ := inf_le_left.trans inf_le_left
  have hW₂ : W ≤ W₂ := inf_le_left.trans inf_le_right
  have he : IsFrame L W (L.res hW₁ e₁) := he₁.restrict hW₁
  have hf : IsFrame N W (N.res hW₂ f₂) := hf₂.restrict hW₂
  -- a|_W = α • e, b|_W = β • f
  have haα := he.coord_smul_frame le_rfl (L.res hWU a)
  rw [res_self] at haα
  have hbβ := hf.coord_smul_frame le_rfl (N.res hWU b)
  rw [res_self] at hbβ
  -- (a ⊗ b)|_W = (α * β) • (e ⊗ f)
  have hab : (AlgebraicGeometry.Scheme.Modules.tensor L N).res hWU (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      (he.coord le_rfl (L.res hWU a) * hf.coord le_rfl (N.res hWU b)) •
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res hW₁ e₁) (N.res hW₂ f₂) := by
    change (AlgebraicGeometry.Scheme.Modules.moduleTensor L N).presheaf.map (homOfLE hWU).op
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) = _
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict]
    change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res hWU a) (N.res hWU b) = _
    conv_lhs => rw [← haα, ← hbβ]
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul]
  -- germ of a ⊗ b under Θ is the germ of α * β
  have hΘ : he.tensorStalkEquivOfFrames hf hyW
      ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ U y hy (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b)) =
        X.presheaf.germ W y hyW
          (he.coord le_rfl (L.res hWU a) * hf.coord le_rfl (N.res hWU b)) := by
    have hres : (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ U y hy
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
        (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hyW
          ((AlgebraicGeometry.Scheme.Modules.tensor L N).res hWU (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b)) :=
      (TopCat.Presheaf.germ_res_apply (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf
        (homOfLE hWU) y hyW (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b)).symm
    have hg : (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hyW
        ((he.coord le_rfl (L.res hWU a) * hf.coord le_rfl (N.res hWU b)) •
          AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res hW₁ e₁) (N.res hW₂ f₂)) =
        X.presheaf.germ W y hyW
            (he.coord le_rfl (L.res hWU a) * hf.coord le_rfl (N.res hWU b)) •
          (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hyW
            (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res hW₁ e₁) (N.res hW₂ f₂)) :=
      germ_smul' (AlgebraicGeometry.Scheme.Modules.tensor L N) hyW _ _
    rw [hres, hab, hg, LinearEquiv.map_smul, he.tensorStalkEquivOfFrames_germ_frame hf hyW,
      smul_eq_mul, mul_one]
  have hT : ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ U y hy
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) :
        (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y)) ↔
      X.presheaf.germ W y hyW
          (he.coord le_rfl (L.res hWU a) * hf.coord le_rfl (N.res hWU b)) ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    (mem_maximalIdeal_smul_top_iff_of_linearEquiv (he.tensorStalkEquivOfFrames hf hyW) _).trans (by rw [hΘ])
  have hL := he.germ_mem_maximalIdeal_smul_iff_coord_res hWU hyW a
  have hN := hf.germ_mem_maximalIdeal_smul_iff_coord_res hWU hyW b
  rw [hT, hL, hN, map_mul]
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mul_iff, not_and_or]

/-- The germ at `y ∈ X_τ` of the tensor power section `τ^{⊗e}` restricted to `X_τ` does not lie in
`𝔪_y` (for `e = 0`, `τ^{⊗0} = 1`; for `e ≥ 1`, `X_{τ^{⊗e}} = X_τ`). -/
theorem germ_res_tensorPowSection_notMem_maximalIdeal_smul (N : X.Modules) [N.IsLineBundle] (τ : Γ(N, ⊤))
    (e : ℕ) {y : X} (hy : y ∈ N.nonvanishingLocus τ) :
    ((AlgebraicGeometry.Scheme.Modules.tensorPow N e).presheaf.germ (N.nonvanishingLocus τ) y hy
        ((AlgebraicGeometry.Scheme.Modules.tensorPow N e).res le_top
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ e)) :
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e).presheaf.stalk y) ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
        (⊤ : Submodule (X.presheaf.stalk y) ((AlgebraicGeometry.Scheme.Modules.tensorPow N e).presheaf.stalk y)) := by
  have hres : (AlgebraicGeometry.Scheme.Modules.tensorPow N e).presheaf.germ (N.nonvanishingLocus τ) y hy
      ((AlgebraicGeometry.Scheme.Modules.tensorPow N e).res le_top
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ e)) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow N e).presheaf.germ ⊤ y trivial
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ e) :=
    TopCat.Presheaf.germ_res_apply (AlgebraicGeometry.Scheme.Modules.tensorPow N e).presheaf
      (homOfLE le_top) y hy _
  have hmem : y ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow N e).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ e) := by
    cases e with
    | zero => rw [nonvanishingLocus_tensorPowSection_zero]; trivial
    | succ e => rw [nonvanishingLocus_tensorPowSection_succ]; exact hy
  rw [hres]
  exact hmem

end AlgebraicGeometry.Scheme.Modules

/-- `X` quasi-compact and quasi-separated, `s ∈ Γ(X_τ, F)`, `W ⊆ X_τ` exactly the nonvanishing locus
of `s` inside `X_τ` ⇒ there are `e` and `σ ∈ Γ(X, F ⊗ N^{⊗e})` with `X_σ ⊓ X_τ = W` (Stacks 01PW(2)). -/
theorem AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishingLocus_inf_eq
    {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (N : X.Modules) [N.IsLineBundle] (τ : Γ(N, ⊤)) (F : X.Modules) [F.IsLineBundle]
    (s : Γ(F, N.nonvanishingLocus τ)) (W : X.Opens) (hWU : W ≤ N.nonvanishingLocus τ)
    (hW : ∀ (y : X) (hy : y ∈ N.nonvanishingLocus τ), y ∈ W ↔
      F.presheaf.germ (N.nonvanishingLocus τ) y hy s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (F.stalk y))) :
    ∃ (e : ℕ) (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e), ⊤)),
      (AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e)).nonvanishingLocus σ ⊓
        N.nonvanishingLocus τ = W := by
  obtain ⟨e, σ, hσ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_restrict_eq N τ F s
  refine ⟨e, σ, ?_⟩
  -- for y ∈ X_τ: y ∈ X_σ ⟺ y ∈ W
  have key : ∀ (y : X) (hy : y ∈ N.nonvanishingLocus τ),
      y ∈ (AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e)).nonvanishingLocus σ ↔ y ∈ W := by
    intro y hy
    rw [hW y hy]
    have h1 : (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow N e)).presheaf.germ ⊤ y trivial σ =
        (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow N e)).presheaf.germ (N.nonvanishingLocus τ) y hy
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s
            ((AlgebraicGeometry.Scheme.Modules.tensorPow N e).presheaf.map
              (CategoryTheory.homOfLE (le_top : N.nonvanishingLocus τ ≤ ⊤)).op
              (AlgebraicGeometry.Scheme.Modules.tensorPowSection τ e))) := by
      rw [← hσ]
      exact (TopCat.Presheaf.germ_res_apply (AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow N e)).presheaf (homOfLE le_top) y hy σ).symm
    have h2 := AlgebraicGeometry.Scheme.Modules.germ_res_tensorPowSection_notMem_maximalIdeal_smul N τ e hy
    refine Iff.trans (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus _ _ _) ?_
    refine not_congr ?_
    refine Iff.trans (by rw [h1]) ?_
    refine Iff.trans (AlgebraicGeometry.Scheme.Modules.germ_moduleTensorSection_mem_maximalIdeal_smul_iff
      F (AlgebraicGeometry.Scheme.Modules.tensorPow N e) s _ hy) ?_
    exact or_iff_left h2
  apply le_antisymm
  · intro y hy
    exact (key y hy.2).mp hy.1
  · intro y hy
    exact ⟨(key y (hWU hy)).mpr hy, hWU hy⟩

end
