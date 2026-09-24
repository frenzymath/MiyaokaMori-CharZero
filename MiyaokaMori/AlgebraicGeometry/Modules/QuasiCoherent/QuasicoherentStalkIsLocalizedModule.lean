import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber

/-! # The stalk of a quasi-coherent sheaf is a localization of its sections

The stalk of a quasi-coherent sheaf `H` at a point `x` of an affine open `W` is the localization of the
module of sections: `germ : Γ(H, W) → H_x` satisfies `IsLocalizedModule p.primeCompl germ` with
`p = hW.primeIdealOf ⟨x, hx⟩ ⊂ Γ(X, W)` (the stalk version of Stacks 01I8 / Hartshorne II.5.4).

Source: Stacks 01I8 (a quasi-coherent sheaf on an affine open is `M~`, with stalks `M_p`). Input:
`QcSectionsBasicOpenLocalization` (sections on basic opens as localizations, two conditions).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (H : X.Modules) (W : X.Opens) (x : X) (hx : x ∈ W)

/-- The `Γ(X, W)`-module structure on the stalk `H_x` of a module sheaf, obtained from the `O_{X,x}`-module
structure by restricting scalars along the germ map `Γ(X, W) → O_{X,x}`. -/
abbrev stalkModuleSections : Module Γ(X, W) (H.presheaf.stalk x) :=
  Module.compHom _ (X.presheaf.germ W x hx).hom

/-- The germ map `Γ(H, W) → H_x` as a `Γ(X, W)`-linear map. -/
def germₗ :
    letI := H.stalkModuleSections W x hx
    Γ(H, W) →ₗ[Γ(X, W)] H.presheaf.stalk x :=
  letI := H.stalkModuleSections W x hx
  { toFun := H.presheaf.germ W x hx
    map_add' := map_add _
    map_smul' := fun r m => PresheafOfModules.germ_smul (R := X.presheaf) H.val x W hx r m }

theorem germₗ_apply (m : Γ(H, W)) : H.germₗ W x hx m = H.presheaf.germ W x hx m := rfl

/-- `PresheafOfModules.germ_smul` spelled with `H.presheaf.germ` (private: the same statement is
`germ_smul'` in `LineBundleNonvanishingLocus`, whose imports are much heavier). -/
private theorem germ_smul_sections (r : Γ(X, W)) (m : Γ(H, W)) :
    H.presheaf.germ W x hx (r • m) = (X.presheaf.germ W x hx r) • H.presheaf.germ W x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) H.val x W hx r m

/-- **The stalk of a quasi-coherent sheaf is the localization of its sections over an affine open**
(Stacks 01I8; Hartshorne II.5.4). Let `H` be a quasi-coherent `O_X`-module, `W ⊆ X` an affine open, `x ∈ W`,
`p := hW.primeIdealOf ⟨x, hx⟩` the prime of `Γ(X, W)` corresponding to `x`. Then the germ map
`Γ(H, W) → H_x` is `Γ(X, W)`-linear (`germₗ`; `Γ(X, W)` acts on `H_x` through `Γ(X, W) → O_{X,x}`) and
exhibits `H_x` as the localization `Γ(H, W)_p` (`IsLocalizedModule p.primeCompl`).

Proof (the three conditions of `IsLocalizedModule`).
(1) For `r ∉ p`, `germ r` is a unit of `O_{X,x}` (`hW.isLocalization_stalk`, `IsLocalization.AtPrime.isUnit_to_map_iff`),
so multiplication by `r` on `H_x` is bijective (`Module.End.isUnit_iff`).
(2) Every `m ∈ H_x` is `germ_U s₀` for some `U ≤ W`, `x ∈ U` (`exists_le_germ_eq`); shrink to a basic open
`D(h) ≤ U`, `h ∈ Γ(X, W)`, `x ∈ D(h)` (`hW.exists_basicOpen_le`), so `h ∉ p` (`mem_basicOpen`); quasi-coherence gives
`t ∈ Γ(H, W)`, `n` with `t|_{D(h)} = h^n • s₀|_{D(h)}` (`exists_pow_smul_eq_map_basicOpen`), hence `h^n • m = germ_W t`
(`germ_res_apply`, `germ_smul`).
(3) If `germ t₁ = germ t₂` then `t₁|_V = t₂|_V` for some `V ∋ x` (`germ_eq`); shrink to `D(h) ≤ V` as before, so
`(t₁ - t₂)|_{D(h)} = 0`, and quasi-coherence gives `h^n • (t₁ - t₂) = 0` (`exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`).
Edge cases: `W = ∅` is impossible (`x ∈ W`); `Γ(H, W) = 0` gives `H_x = 0`, all conditions trivial. -/
theorem isLocalizedModule_germₗ_of_isQuasicoherent [H.IsQuasicoherent] (hW : IsAffineOpen W) :
    letI := H.stalkModuleSections W x hx
    IsLocalizedModule (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (H.germₗ W x hx) := by
  letI := H.stalkModuleSections W x hx
  set p := hW.primeIdealOf ⟨x, hx⟩ with hp
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : W)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal := hW.isLocalization_stalk ⟨x, hx⟩
  have hunit : ∀ h : Γ(X, W), h ∈ p.asIdeal.primeCompl ↔ IsUnit (X.presheaf.germ W x hx h) := fun h =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) p.asIdeal h).symm
  have hsmul : ∀ (r : Γ(X, W)) (m : H.presheaf.stalk x),
      r • m = (X.presheaf.germ W x hx r) • m := fun _ _ => rfl
  constructor
  · -- multiplication by r ∉ p is bijective on the stalk: germ r is a unit of O_{X,x}
    intro s
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := (hunit s).mp s.2
    constructor
    · intro m₁ m₂ h
      simp only [Module.algebraMap_end_apply, hsmul, ← hu] at h
      have := congrArg (fun m => (↑u⁻¹ : X.presheaf.stalk x) • m) h
      simpa [smul_smul] using this
    · intro m
      refine ⟨(↑u⁻¹ : X.presheaf.stalk x) • m, ?_⟩
      simp [Module.algebraMap_end_apply, hsmul, ← hu, smul_smul]
  · -- every germ is, up to a power of some h ∉ p, the germ of a section over W
    intro m
    obtain ⟨U, hUW, hxU, s₀, rfl⟩ := H.presheaf.exists_le_germ_eq m hx
    obtain ⟨h, hhU, hxh⟩ := hW.exists_basicOpen_le ⟨x, hxU⟩ hx
    obtain ⟨n, t, ht⟩ := Scheme.Modules.exists_pow_smul_eq_map_basicOpen H hW h
      (H.presheaf.map (homOfLE hhU).op s₀)
    have hhp : h ∈ p.asIdeal.primeCompl := (hunit h).mpr ((X.mem_basicOpen h x hx).mp hxh)
    refine ⟨(t, ⟨h ^ n, pow_mem hhp n⟩), ?_⟩
    show (h ^ n) • H.presheaf.germ U x hxU s₀ = H.presheaf.germ W x hx t
    have hxb : x ∈ X.basicOpen h := hxh
    rw [← H.presheaf.germ_res_apply (homOfLE (X.basicOpen_le h)) x hxb t, ht,
      germ_smul_sections H (X.basicOpen h) x hxb, map_pow,
      X.presheaf.germ_res_apply, H.presheaf.germ_res_apply, hsmul, map_pow]
  · -- germs agree ⇒ sections agree after multiplying by a power of some h ∉ p
    intro t₁ t₂ h12
    obtain ⟨V, hxV, iU, iV, e⟩ := H.presheaf.germ_eq x hx hx t₁ t₂ h12
    obtain ⟨h, hhV, hxh⟩ := hW.exists_basicOpen_le ⟨x, hxV⟩ hx
    have hzero : H.presheaf.map (homOfLE (X.basicOpen_le h)).op (t₁ - t₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      have := congrArg (H.presheaf.map (homOfLE hhV).op) e
      rw [← H.presheaf.map_comp_apply, ← H.presheaf.map_comp_apply] at this
      exact this
    obtain ⟨n, hn⟩ := Scheme.Modules.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero H hW h
      (t₁ - t₂) hzero
    have hhp : h ∈ p.asIdeal.primeCompl := (hunit h).mpr ((X.mem_basicOpen h x hx).mp hxh)
    refine ⟨⟨h ^ n, pow_mem hhp n⟩, ?_⟩
    show (h ^ n) • t₁ = (h ^ n) • t₂
    rw [← sub_eq_zero, ← smul_sub]
    exact hn

end AlgebraicGeometry.Scheme.Modules

end
