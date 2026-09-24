import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection

/-! # Germ criterion for a tensor with a frame

**Germ criterion for a tensor with a frame**: on an open `W ∋ y`, let `f ∈ Γ(N, W)` be a frame of `N`
(`IsFrame`) and `s ∈ Γ(L, W)` any section. If the germ at `y` of `s ⊗ f ∈ Γ(L ⊗ N, W)`
(`moduleTensorSection`, `Modules.tensor`) lies in `𝔪_y · (L ⊗ N)_y`, then the germ of `s` lies in
`𝔪_y · L_y` (and conversely).

Proof (Stacks 01CB, tensor of stalks; one-generator freeness of a frame): the composite linear equivalence
`(L ⊗ N)_y ≅ L_y ⊗ N_y ≅ L_y ⊗ 𝒪_y ≅ L_y` (`moduleStalkLinearEquiv` along `tensorIsoTensorObj`, `tensorStalkEquiv`,
`IsFrame.stalkEquiv` for `N`, `TensorProduct.rid`) sends the germ of `s ⊗ f` to `s_y ⊗ f_y ↦ s_y ⊗ 1 ↦ s_y`
(`tensorStalkEquiv_germ_tensorSections`, `IsFrame.stalkEquiv_apply` with `1 • f_y = f_y`), and a linear equivalence
carries `𝔪_y • ⊤` onto `𝔪_y • ⊤` (`Submodule.mem_smul_top_linearEquiv_iff`). No line-bundle hypothesis on `L` is
needed. Used in the coordinate-divisor computation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `(L ⊗ N)_y ≃ L_y` along a frame `f` of `N` at `y`: `tensorIsoTensorObj` on stalks, Stacks 01CB
(`tensorStalkEquiv`), `N_y ≃ 𝒪_y` (`IsFrame.stalkEquiv`), and `L_y ⊗ 𝒪_y ≃ L_y` (`TensorProduct.rid`). -/
noncomputable def IsFrame.tensorStalkEquivRight (L : X.Modules) {N : X.Modules} {W : X.Opens} {f : Γ(N, W)}
    (hf : IsFrame N W f) {y : X} (hy : y ∈ W) :
    (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y ≃ₗ[X.presheaf.stalk y] L.presheaf.stalk y :=
  moduleStalkLinearEquiv X y (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N) ≪≫ₗ
    tensorStalkEquiv L N y ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl (X.presheaf.stalk y) (L.presheaf.stalk y)) (hf.stalkEquiv hy).symm ≪≫ₗ
    TensorProduct.rid (X.presheaf.stalk y) (L.presheaf.stalk y)

/-- The equivalence sends the germ of `s ⊗ f` to the germ of `s`. -/
theorem IsFrame.tensorStalkEquivRight_germ_moduleTensorSection (L : X.Modules) {N : X.Modules} {W : X.Opens}
    {f : Γ(N, W)} (hf : IsFrame N W f) {y : X} (hy : y ∈ W) (s : Γ(L, W)) :
    hf.tensorStalkEquivRight L hy
        ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s f)) =
      L.presheaf.germ W y hy s := by
  have step1 : moduleStalkLinearEquiv X y (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N)
      ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s f)) =
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections L N W s f) :=
    moduleStalkLinearEquiv_germ X y (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N) W hy
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s f)
  have step2 : tensorStalkEquiv L N y
      ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections L N W s f)) =
      (L.presheaf.germ W y hy) s ⊗ₜ[X.presheaf.stalk y] (N.presheaf.germ W y hy) f :=
    tensorStalkEquiv_germ_tensorSections L N y W hy s f
  have h2 : (hf.stalkEquiv hy).symm (N.presheaf.germ W y hy f) = 1 := by
    rw [LinearEquiv.symm_apply_eq, IsFrame.stalkEquiv_apply, one_smul]
  unfold IsFrame.tensorStalkEquivRight
  simp only [LinearEquiv.trans_apply]
  rw [step1, step2, TensorProduct.congr_tmul, LinearEquiv.refl_apply, h2, TensorProduct.rid_tmul, one_smul]

/-- **Germ criterion for a tensor with a frame**: `(s ⊗ f)_y ∈ 𝔪_y • ⊤ ↔ s_y ∈ 𝔪_y • ⊤` when `f` is a frame of `N`. -/
theorem IsFrame.germ_moduleTensorSection_mem_maximalIdeal_smul_iff (L : X.Modules) {N : X.Modules} {W : X.Opens}
    {f : Γ(N, W)} (hf : IsFrame N W f) {y : X} (hy : y ∈ W) (s : Γ(L, W)) :
    (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s f) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y)) ↔
      L.presheaf.germ W y hy s ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (L.presheaf.stalk y)) := by
  rw [← Submodule.mem_smul_top_linearEquiv_iff (hf.tensorStalkEquivRight L hy),
    hf.tensorStalkEquivRight_germ_moduleTensorSection L hy s]

/-- The direction used for coverage: if `s ⊗ f` vanishes at `y` (`f` a frame), then `s` vanishes at `y`. -/
theorem IsFrame.germ_mem_maximalIdeal_smul_of_germ_moduleTensorSection_mem (L : X.Modules) {N : X.Modules}
    {W : X.Opens} {f : Γ(N, W)} (hf : IsFrame N W f) {y : X} (hy : y ∈ W) (s : Γ(L, W))
    (h : (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s f) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y))) :
    L.presheaf.germ W y hy s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
        (⊤ : Submodule (X.presheaf.stalk y) (L.presheaf.stalk y)) :=
  (hf.germ_moduleTensorSection_mem_maximalIdeal_smul_iff L hy s).mp h

end AlgebraicGeometry.Scheme.Modules

end
