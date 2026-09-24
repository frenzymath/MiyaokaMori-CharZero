import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesTensorStalk
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt

/-! # Germ criteria for `BasedJet.exists_pieceSection_generatesAt` (helper of `JetWeightComponentEqCoefficient`)

Everything here is stated at the variable level (`X` a scheme, `M N : X.Modules`).
The question "does the germ of a local section at `y` lie in `𝔪_y • ⊤`" (this is `IsZeroAt` for global sections and the
negation of `GeneratesAt` for local sections) is invariant under

* an isomorphism of module sheaves applied on sections (`germ_hom_app_mem_maximalIdeal_smul_iff_of_iso`,
  via `moduleStalkLinearEquiv`);
* tensoring **on the left** with a frame: `(a ⊗ t)_y ∈ 𝔪_y • ⊤ ↔ t_y ∈ 𝔪_y • ⊤` when `a` is a frame of `M` on `W`
  (`IsFrame.germ_tensorSections_mem_maximalIdeal_smul_iff_left`; Stacks 01CB `tensorStalkEquiv`, then `M_y ≃ 𝒪_y`
  by `IsFrame.stalkEquiv` and `𝒪_y ⊗ N_y ≃ N_y` by `TensorProduct.lid`). The right-handed version for
  `Modules.tensor`/`moduleTensorSection` is `IsFrame.germ_moduleTensorSection_mem_maximalIdeal_smul_iff`
  (`CoordinatesNotAllVanish_LocalGenerators_GermTensorFrame.lean`); this one is for the monoidal `⊗` and
  `tensorSections`, frame on the left, as needed for `M ⊗ (L^∨)^{⊗m}` with `M = ρ^*A` framed;
* restriction of a section to a smaller open containing `y` (`germ_res_mem_maximalIdeal_smul_iff`,
  `TopCat.Presheaf.germ_res_apply`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- An isomorphism of module sheaves, applied on sections over `W`, preserves membership of the germ at `y` in
`𝔪_y • ⊤` (the stalk map of an isomorphism is a linear isomorphism, `moduleStalkLinearEquiv`). -/
theorem germ_hom_app_mem_maximalIdeal_smul_iff_of_iso {M N : X.Modules} (θ : M ≅ N) (W : X.Opens) {y : X}
    (hy : y ∈ W) (t : Γ(M, W)) :
    N.presheaf.germ W y hy (θ.hom.app W t) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (N.presheaf.stalk y)) ↔
      M.presheaf.germ W y hy t ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (M.presheaf.stalk y)) := by
  rw [← Submodule.mem_smul_top_linearEquiv_iff (moduleStalkLinearEquiv X y θ), moduleStalkLinearEquiv_germ]

/-- Restricting a section to a smaller open containing `y` does not change its germ at `y`. -/
theorem germ_res_mem_maximalIdeal_smul_iff (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) {y : X} (hy : y ∈ W')
    (t : Γ(M, W)) :
    M.presheaf.germ W' y hy (M.res h t) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (M.presheaf.stalk y)) ↔
      M.presheaf.germ W y (h hy) t ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (M.presheaf.stalk y)) := by
  rw [show M.presheaf.germ W' y hy (M.res h t) = M.presheaf.germ W y (h hy) t from
    TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE h) y hy t]

/-- `(M ⊗ N)_y ≃ N_y` along a frame `a` of `M` at `y`: Stacks 01CB (`tensorStalkEquiv`), `M_y ≃ 𝒪_y`
(`IsFrame.stalkEquiv`), and `𝒪_y ⊗ N_y ≃ N_y` (`TensorProduct.lid`). -/
noncomputable def IsFrame.tensorStalkEquivLeft {M : X.Modules} (N : X.Modules) {W : X.Opens} {a : Γ(M, W)}
    (hf : IsFrame M W a) {y : X} (hy : y ∈ W) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N).presheaf.stalk y
      ≃ₗ[X.presheaf.stalk y] N.presheaf.stalk y :=
  tensorStalkEquiv M N y ≪≫ₗ
    TensorProduct.congr (hf.stalkEquiv hy).symm (LinearEquiv.refl (X.presheaf.stalk y) (N.presheaf.stalk y)) ≪≫ₗ
    TensorProduct.lid (X.presheaf.stalk y) (N.presheaf.stalk y)

/-- The equivalence sends the germ of `a ⊗ t` to the germ of `t`. -/
theorem IsFrame.tensorStalkEquivLeft_germ_tensorSections {M : X.Modules} (N : X.Modules) {W : X.Opens}
    {a : Γ(M, W)} (hf : IsFrame M W a) {y : X} (hy : y ∈ W) (t : Γ(N, W)) :
    hf.tensorStalkEquivLeft N hy
        ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N).presheaf.germ W y hy
          (AlgebraicGeometry.Scheme.Modules.tensorSections M N W a t)) =
      N.presheaf.germ W y hy t := by
  have h2 : (hf.stalkEquiv hy).symm (M.presheaf.germ W y hy a) = 1 := by
    rw [LinearEquiv.symm_apply_eq, IsFrame.stalkEquiv_apply, one_smul]
  have step : tensorStalkEquiv M N y
      ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N W a t)) =
      (M.presheaf.germ W y hy) a ⊗ₜ[X.presheaf.stalk y] (N.presheaf.germ W y hy) t :=
    tensorStalkEquiv_germ_tensorSections M N y W hy a t
  unfold IsFrame.tensorStalkEquivLeft
  simp only [LinearEquiv.trans_apply]
  erw [step]
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, h2, TensorProduct.lid_tmul, one_smul]

/-- **Germ criterion for a tensor with a frame on the left**: `(a ⊗ t)_y ∈ 𝔪_y • ⊤ ↔ t_y ∈ 𝔪_y • ⊤` when `a` is a
frame of `M` on `W` (monoidal `⊗`, `tensorSections`). -/
theorem IsFrame.germ_tensorSections_mem_maximalIdeal_smul_iff_left {M : X.Modules} (N : X.Modules) {W : X.Opens}
    {a : Γ(M, W)} (hf : IsFrame M W a) {y : X} (hy : y ∈ W) (t : Γ(N, W)) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N W a t) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y)
            ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N).presheaf.stalk y)) ↔
      N.presheaf.germ W y hy t ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (N.presheaf.stalk y)) := by
  rw [← Submodule.mem_smul_top_linearEquiv_iff (hf.tensorStalkEquivLeft N hy),
    hf.tensorStalkEquivLeft_germ_tensorSections N hy t]

end AlgebraicGeometry.Scheme.Modules

end
