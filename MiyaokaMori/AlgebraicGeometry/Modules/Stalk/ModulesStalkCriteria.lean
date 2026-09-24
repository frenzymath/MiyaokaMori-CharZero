import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerTopLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber

/-! # Stalkwise criteria for sheaves of modules

Four "stalkwise" criteria for `O_X`-modules, proved directly (without the exactness of the stalk
functor):

* `hom_ext_of_stalkMap`: two morphisms that agree on every stalk are equal (sections of a sheaf are
  determined by their germs, `TopCat.Presheaf.section_ext`);
* `epi_of_stalkMap_surjective`: surjective on every stalk ⇒ epimorphism (Mathlib
  `locally_surjective_iff_surjective_on_stalks` + `isLocallySurjective_iff_epi`; the converse is
  `stalkMap_surjective_of_epi`);
* `stalkMap_exact_of_shortExact` / `stalkMap_injective_of_shortExact` / `stalkMap_surjective_of_shortExact`:
  a short exact sequence is exact on stalks, injective on the left and surjective on the right.
  Exactness and injectivity are obtained by taking germs in the section-level statement
  `ModulesLocLiftAux.sections_of_exact_mono` (`f` injective and `ker g ⊆ im f` on every open):
  a stalk element is a germ, and a germ vanishes iff the section vanishes on a smaller open;
* `exists_stalk_basis_fin`: a locally free module of finite type and pointwise rank `r` has, at
  every point, a stalk with a basis indexed by `Fin r` (`exists_restrict_iso_free_fin` gives
  `E|_U ≅ O_U^{Fin r}`, the stalk of a free sheaf has its standard basis
  `FreeStalk.linearIndependent_b` / `span_b_eq_top`, transported semilinearly along
  `moduleRestrictStalkEquiv`).

Source: Stacks 01AJ / 007Z (elementary form of the exactness of the stalk functor), Stacks 01CB.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.ModulesStalkCriteria

open AlgebraicGeometry AlgebraicGeometry.Divisors AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A morphism is determined by its stalk maps. -/
theorem hom_ext_of_stalkMap {M N : X.Modules} {φ ψ : M ⟶ N}
    (h : ∀ x : X, moduleStalkMap X x φ = moduleStalkMap X x ψ) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) U
  intro x hx
  have h1 := moduleStalkMap_germ X x φ U hx s
  have h2 := moduleStalkMap_germ X x ψ U hx s
  rw [h x] at h1
  exact h1.symm.trans h2

/-- Surjective on every stalk ⇒ epimorphism. -/
theorem epi_of_stalkMap_surjective {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, Function.Surjective (moduleStalkMap X x φ)) : Epi φ := by
  have hloc : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr h
  have : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map this

section ShortExact

variable {S : CategoryTheory.ShortComplex X.Modules} (hS : S.ShortExact) (x : X)

include hS

/-- The right map of a short exact sequence is surjective on stalks. -/
theorem stalkMap_surjective_of_shortExact : Function.Surjective (moduleStalkMap X x S.g) := by
  have := hS.epi_g
  exact MiyaokaMori.FreeStalk.stalkMap_surjective_of_epi S.g x

/-- The left map of a short exact sequence is injective on stalks. -/
theorem stalkMap_injective_of_shortExact : Function.Injective (moduleStalkMap X x S.f) := by
  have := hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨U, hxU, t, rfl⟩ := S.X₁.presheaf.exists_germ_eq z
  rw [moduleStalkMap_germ] at hz
  obtain ⟨W, hxW, iU, _, hW⟩ := S.X₂.presheaf.germ_eq x hxU hxU (S.f.app U t) 0
    (by rw [hz, map_zero])
  rw [map_zero] at hW
  have h1 : S.f.app W (S.X₁.presheaf.map iU.op t) = 0 := by
    rw [← hW]
    exact PresheafOfModules.naturality_apply S.f.val iU.op t
  have h2 : S.X₁.presheaf.map iU.op t = 0 :=
    (ModulesLocLiftAux.sections_of_exact_mono S hS.exact W).1 (by rw [h1, map_zero])
  rw [← S.X₁.presheaf.germ_res_apply iU x hxW t, h2, map_zero]

/-- A short exact sequence is exact on stalks: `ker g_x = im f_x`. -/
theorem stalkMap_exact_of_shortExact :
    Function.Exact (moduleStalkMap X x S.f) (moduleStalkMap X x S.g) := by
  have := hS.mono_f
  intro y
  constructor
  · intro hy
    obtain ⟨U, hxU, s, rfl⟩ := S.X₂.presheaf.exists_germ_eq y
    rw [moduleStalkMap_germ] at hy
    obtain ⟨W, hxW, iU, _, hW⟩ := S.X₃.presheaf.germ_eq x hxU hxU (S.g.app U s) 0
      (by rw [hy, map_zero])
    rw [map_zero] at hW
    have hW' : S.g.app W (S.X₂.presheaf.map iU.op s) = 0 := by
      rw [← hW]
      exact PresheafOfModules.naturality_apply S.g.val iU.op s
    obtain ⟨z, hz⟩ := (ModulesLocLiftAux.sections_of_exact_mono S hS.exact W).2 _ hW'
    refine ⟨S.X₁.presheaf.germ W x hxW z, ?_⟩
    rw [moduleStalkMap_germ, hz]
    exact S.X₂.presheaf.germ_res_apply iU x hxW s
  · rintro ⟨z, rfl⟩
    obtain ⟨U, hxU, t, rfl⟩ := S.X₁.presheaf.exists_germ_eq z
    rw [moduleStalkMap_germ, moduleStalkMap_germ]
    have h0 : S.g.app U (S.f.app U t) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, S.zero,
        Scheme.Modules.Hom.zero_app]
      rfl
    rw [h0]
    exact map_zero _

end ShortExact

/-- The stalk at `y` of the free sheaf `O_Y^{(I)}` (`I` finite) has a basis indexed by `I`. -/
private theorem free_stalk_basis {Y : AlgebraicGeometry.Scheme.{u}} (I : Type u) [Finite I]
    (y : Y) :
    Nonempty (Module.Basis I (Y.presheaf.stalk y)
      ((MiyaokaMori.FreeStalk.freeM Y I).presheaf.stalk y)) :=
  ⟨Module.Basis.mk (MiyaokaMori.FreeStalk.linearIndependent_b I y)
    (MiyaokaMori.FreeStalk.span_b_eq_top I y).ge⟩

/-- A locally free module of finite type and pointwise rank `r` has, at every point, a stalk with
a basis indexed by `Fin r`. -/
theorem exists_stalk_basis_fin (E : X.Modules) (r : ℕ) [E.IsLocallyFree] [E.IsFiniteType]
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = r) (x : X) :
    Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (E.presheaf.stalk x)) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := AlgebraicGeometry.Scheme.Modules.exists_restrict_iso_free_fin E r hr x
  let y : U := ⟨x, hxU⟩
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme
    (MiyaokaMori.FreeStalk.freeM U.toScheme (ULift.{u} (Fin r))) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  obtain ⟨b0⟩ := free_stalk_basis (Y := U.toScheme) (ULift.{u} (Fin r)) y
  let L := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e).toLinearEquiv
  let b1 := b0.map L.symm
  let σ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  obtain ⟨b2⟩ := MiyaokaMori.basis_of_semilinearEquiv
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y) b1
  exact ⟨b2.reindex (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)⟩

end MiyaokaMori.ModulesStalkCriteria

end
