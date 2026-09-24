import MiyaokaMori.Prelude
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-! # Homology commutes with localization

**Statement.** Let `f : R →+* S` be a ring homomorphism with `S` the localization of `R` at a
submonoid `T` (`IsLocalization T S` for the algebra structure `f.toAlgebra`). Then for every cochain
complex `K` of `R`-modules and every degree `i`, the canonical `R`-linear map
`H^i(K) → H^i(K ⊗_R S)` (restrict scalars of the `S`-module `H^i(K ⊗_R S)`) is a localization of
modules at `T` (`IsLocalizedModule T`), i.e. `H^i(K ⊗_R S) ≅ H^i(K) ⊗_R S ≅ T⁻¹ H^i(K)`.
Also: the adjunction transpose `S ⊗_R M₀ → N₀` of any `R`-linear localization map `M₀ → N₀` is an
isomorphism.

**Proof** (Stacks 00CS / Atiyah–Macdonald 3.3 + exactness of localization, Stacks 00CS(2)):
1. `S` is a flat `R`-module (`IsLocalization.flat`), so `extendScalars f = S ⊗_R -` preserves
   monomorphisms (`Module.Flat.lTensor_preserves_injective_linearMap`); being a left adjoint it
   preserves cokernels; hence it preserves homology
   (`Functor.preservesHomology_of_preservesMonos_and_cokernels`) and
   `H^i(K ⊗_R S) ≅ S ⊗_R H^i(K)` (`ShortComplex.mapHomologyIso`).
2. The unit `N → S ⊗_R N`, `x ↦ 1 ⊗ x`, is the base change of `N` along `R → S`
   (`IsBaseChange.of_equiv` with the identity), and base change along a localization is the
   localization of modules (`isLocalizedModule_iff_isBaseChange`).
3. Compose (transport `IsLocalizedModule` along the linear isomorphism of step 1).
4. Transpose: `S ⊗ M₀ → N₀` composed with the unit is the given localization map; two
   localization maps of the same module differ by a unique isomorphism
   (`IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp`), and `restrictScalars` reflects
   isomorphisms. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section
namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem extendScalars_map_injective [Module.Flat R ((restrictScalars f).obj (of S S))]
    {M N : ModuleCat.{u} R} (l : M ⟶ N) (hl : Function.Injective l) :
    Function.Injective ((extendScalars f).map l) := by
  show Function.Injective (l.hom.lTensor ((restrictScalars f).obj (of S S)))
  exact Module.Flat.lTensor_preserves_injective_linearMap l.hom hl

theorem extendScalars_preservesMonomorphisms [Module.Flat R ((restrictScalars f).obj (of S S))] :
    (extendScalars.{u, u, u} f).PreservesMonomorphisms where
  preserves l hl := (mono_iff_injective ((extendScalars f).map l)).2
    (extendScalars_map_injective f l ((mono_iff_injective l).1 hl))

theorem extendScalars_preservesHomology [(extendScalars.{u, u, u} f).PreservesMonomorphisms] :
    (extendScalars.{u, u, u} f).PreservesHomology := by
  have : (extendScalars.{u, u, u} f).Additive := (extendRestrictScalarsAdj f).left_adjoint_additive
  have := (extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

theorem flat_restrictScalars_of_flat_toAlgebra
    (hflat : letI := f.toAlgebra; Module.Flat R S) :
    Module.Flat R ((restrictScalars f).obj (of S S)) := by
  letI := f.toAlgebra
  exact Module.Flat.of_linearEquiv (M := S)
    { toFun := fun x => (x : S), invFun := fun x => x, map_add' := fun _ _ => rfl,
      map_smul' := fun r (x : S) => by
        show f r * x = r • x
        exact (Algebra.smul_def r x).symm,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

set_option backward.isDefEq.respectTransparency false in
theorem isLocalizedModule_extendRestrictScalarsAdj_unit (T : Submonoid R)
    (hloc : letI := f.toAlgebra; IsLocalization T S) (N : ModuleCat.{u} R) :
    IsLocalizedModule T ((extendRestrictScalarsAdj f).unit.app N).hom := by
  letI := f.toAlgebra
  letI : Module S ((extendScalars f ⋙ restrictScalars f).obj N) :=
    inferInstanceAs (Module S ((extendScalars f).obj N))
  haveI : IsScalarTower R S ((extendScalars f ⋙ restrictScalars f).obj N) :=
    ⟨fun r s x => by
      show (f r * s) • x = f r • (s • x)
      rw [mul_smul]⟩
  rw [isLocalizedModule_iff_isBaseChange T S]
  refine IsBaseChange.of_equiv (LinearEquiv.refl S _) fun x => ?_
  rfl

/-- homology of `K ⊗_R S` is the localization of the homology of `K` -/
theorem exists_isLocalizedModule_homology_extendScalars (T : Submonoid R)
    (hloc : letI := f.toAlgebra; IsLocalization T S)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ∃ ψ : K.homology i →ₗ[R] (restrictScalars f).obj
      ((((extendScalars f).mapHomologicalComplex _).obj K).homology i),
      IsLocalizedModule T ψ := by
  have hflat : Module.Flat R ((restrictScalars f).obj (of S S)) :=
    flat_restrictScalars_of_flat_toAlgebra f (by
      letI := f.toAlgebra
      haveI := hloc
      exact IsLocalization.flat S T)
  have := extendScalars_preservesMonomorphisms f
  have := extendScalars_preservesHomology f
  let e : (((extendScalars f).mapHomologicalComplex _).obj K).homology i ≅
      (extendScalars f).obj (K.homology i) :=
    (K.sc i).mapHomologyIso (extendScalars f)
  refine ⟨((restrictScalars f).map e.inv).hom ∘ₗ ((extendRestrictScalarsAdj f).unit.app (K.homology i)).hom, ?_⟩
  have := isLocalizedModule_extendRestrictScalarsAdj_unit f T hloc (K.homology i)
  exact IsLocalizedModule.of_linearEquiv T _ ((restrictScalars f).mapIso e.symm).toLinearEquiv

/-- the adjunction transpose of a localization map is an isomorphism -/
theorem isIso_homEquiv_symm_of_isLocalizedModule (T : Submonoid R)
    (hloc : letI := f.toAlgebra; IsLocalization T S) {M₀ : ModuleCat.{u} R} {N₀ : ModuleCat.{u} S}
    (α : M₀ ⟶ (restrictScalars f).obj N₀) (hα : IsLocalizedModule T α.hom) :
    IsIso (((extendRestrictScalarsAdj f).homEquiv M₀ N₀).symm α) := by
  set τ := ((extendRestrictScalarsAdj f).homEquiv M₀ N₀).symm α with hτdef
  have hτ : (extendRestrictScalarsAdj f).unit.app M₀ ≫ (restrictScalars f).map τ = α := by
    have h1 : ((extendRestrictScalarsAdj f).homEquiv M₀ N₀) τ = α := Equiv.apply_symm_apply _ _
    rwa [Adjunction.homEquiv_unit] at h1
  have hu := isLocalizedModule_extendRestrictScalarsAdj_unit f T hloc M₀
  have hcomp : ((restrictScalars f).map τ).hom ∘ₗ
      ((extendRestrictScalarsAdj f).unit.app M₀).hom = α.hom := by
    rw [← ModuleCat.hom_comp, hτ]
  have hbij : Function.Bijective ((restrictScalars f).map τ).hom := by
    haveI : IsLocalizedModule T (((restrictScalars f).map τ).hom ∘ₗ
        ((extendRestrictScalarsAdj f).unit.app M₀).hom) := hcomp ▸ hα
    have e := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp T
      ((extendRestrictScalarsAdj f).unit.app M₀).hom ((restrictScalars f).map τ).hom
    rw [← e]
    exact LinearEquiv.bijective _
  have : IsIso ((restrictScalars f).map τ) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact isIso_of_reflects_iso τ (restrictScalars f)

end ModuleCat

end
