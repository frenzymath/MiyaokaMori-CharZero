import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentStalkIsLocalizedModule
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.DenominatorMapsAssembly

/-! # A morphism of quasi-coherent modules that is injective on sections over an affine open cover is a
monomorphism

For quasi-coherent `M`, `M'` on a scheme `Y` and `φ : M ⟶ M'`: if `φ.app W` is injective for every member `W`
of a family of affine opens covering `Y`, then `φ` is a monomorphism. (Stacks 01I8 + "mono ⇔ injective on stalks".)

Proof. Monomorphisms of module sheaves are detected on stalks (`Modules.mono_of_stalkMap_injective`,
`DenominatorMapsAssembly`). For `y ∈ W` with `W` affine, the stalk `M_y` is the localization of `Γ(M, W)` at
the prime `p_y ⊂ Γ(Y, W)` of `y` (`isLocalizedModule_germₗ_of_isQuasicoherent`, Stacks 01I8), and likewise for `M'`;
the stalk map `φ_y` is `Γ(Y, W)`-linear and agrees with `φ.app W` on germs (`moduleStalkMap_germ`), so by the
universal property of localization it *is* `IsLocalizedModule.map _ _ _ (φ.app W)`, which is injective when
`φ.app W` is (`IsLocalizedModule.map_injective`: localization is exact).

Edge cases: `Y = ∅` (no stalks, `Mono` trivially — `mono_of_stalkMap_injective` with an empty hypothesis);
`M = 0` (`φ.app W` injective on the zero module, stalks zero).

Source: Stacks 01I8 (sections and stalks of quasi-coherent sheaves on affine opens); Hartshorne II.5.4;
Stacks 01AG (a morphism of sheaves is a monomorphism iff it is injective on stalks). Used to reduce
`Mono` to injectivity of sections over affine opens `π⁻¹U`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- **Stalk maps of quasi-coherent modules are injective at points of an affine open on whose sections the
morphism is injective** (Stacks 01I8: the stalk is the localization of the sections, and localization is exact). -/
theorem stalkMap_injective_of_app_injective {M M' : Y.Modules} [M.IsQuasicoherent] [M'.IsQuasicoherent]
    (φ : M ⟶ M') {W : Y.Opens} (hW : AlgebraicGeometry.IsAffineOpen W) {y : Y} (hy : y ∈ W)
    (hinj : Function.Injective (φ.app W)) :
    Function.Injective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y φ) := by
  letI := M.stalkModuleSections W y hy
  letI := M'.stalkModuleSections W y hy
  have hM := M.isLocalizedModule_germₗ_of_isQuasicoherent W y hy hW
  have hM' := M'.isLocalizedModule_germₗ_of_isQuasicoherent W y hy hW
  set p := (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl with hp
  -- `φ.app W` as a `Γ(Y, W)`-linear map
  let ψ : Γ(M, W) →ₗ[Γ(Y, W)] Γ(M', W) :=
    { toFun := φ.app W
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r m => AlgebraicGeometry.Scheme.Modules.Hom.app_smul φ r m }
  -- the stalk map as a `Γ(Y, W)`-linear map
  let Φ : M.presheaf.stalk y →ₗ[Γ(Y, W)] M'.presheaf.stalk y :=
    { toFun := AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y φ
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r m => (AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y φ).map_smul (Y.presheaf.germ W y hy r) m }
  have hΦ : Φ = IsLocalizedModule.map p (M.germₗ W y hy) (M'.germₗ W y hy) ψ := by
    apply IsLocalizedModule.ext p (M.germₗ W y hy) (IsLocalizedModule.map_units (M'.germₗ W y hy))
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, IsLocalizedModule.map_apply]
    exact AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ Y y φ W hy m
  intro a b hab
  have h : Φ a = Φ b := hab
  rw [hΦ] at h
  exact IsLocalizedModule.map_injective p (M.germₗ W y hy) (M'.germₗ W y hy) ψ hinj h

/-- **A morphism of quasi-coherent modules injective on sections over an affine open cover is a monomorphism.**
`𝒰 : ι → Y.Opens` is a family of affine opens covering `Y` (every point lies in some `𝒰 i`), and `φ.app (𝒰 i)` is
injective for every `i`. -/
theorem mono_of_app_injective_of_isAffineOpen {M M' : Y.Modules} [M.IsQuasicoherent] [M'.IsQuasicoherent]
    (φ : M ⟶ M') {ι : Type*} (𝒰 : ι → Y.Opens) (h𝒰 : ∀ i, AlgebraicGeometry.IsAffineOpen (𝒰 i))
    (hcov : ∀ y : Y, ∃ i, y ∈ 𝒰 i) (hinj : ∀ i, Function.Injective (φ.app (𝒰 i))) : Mono φ := by
  apply mono_of_stalkMap_injective
  intro y
  obtain ⟨i, hi⟩ := hcov y
  exact stalkMap_injective_of_app_injective φ (h𝒰 i) hi (hinj i)

end AlgebraicGeometry.Scheme.Modules

end
