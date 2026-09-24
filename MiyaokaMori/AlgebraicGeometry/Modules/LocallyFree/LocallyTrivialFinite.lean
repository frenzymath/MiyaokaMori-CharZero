import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit

/-! # Locally trivial sheaves are locally free of finite type

Let `M` be a sheaf of modules on a scheme `X`. If every point has an open neighbourhood `U` with
`M|_U ≅ O_U`, then `M` is locally free (Mathlib's site-theoretic `SheafOfModules.IsLocallyFree`) and
of finite type (`SheafOfModules.IsFiniteType`). More generally, if every point lies in the image of an
open immersion `g : Y ⟶ X` with `M|_Y` isomorphic to a free sheaf on a finite index type, then `M` is
locally free of finite type (`isLocallyFree_and_isFiniteType_of_restrict_free_finite`).

Design: Mathlib's `IsLocallyFree` / `IsFiniteType` are stated with generating sections on the site
`Over U`, separated from "restricts to `O_U` on an open subscheme" by `overEquiv`.
`LocallyFreeOfRestrictFreeCover` proves the locally free half, but its key lemma `over_gen` only gives
`∃ σ, IsIso σ.π` and loses the index type of `σ`, so finite type cannot be extracted from it; here the
same proof is written so as to give both conclusions. The statements do not mention line bundles.

References: Stacks 01C6, 01B5.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- `Y`-modules → `X.ringCatSheaf.over (image of g)`-modules: restrict along `image ≅ Y`, then apply
`overEquiv`. -/
def overOfOpenImmersion {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} (X.ringCatSheaf.over g.opensRange) :=
  restrictFunctor g.isoOpensRange.inv ⋙ (overEquiv g.opensRange).inverse

instance overOfOpenImmersion_preservesColimits {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    PreservesColimitsOfSize.{u, u} (overOfOpenImmersion g) := by
  have h1 : PreservesColimitsOfSize.{u, u} (restrictFunctor g.isoOpensRange.inv) := inferInstance
  have h2 : PreservesColimitsOfSize.{u, u} (overEquiv g.opensRange).inverse := inferInstance
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h1 h2

/-- If the restriction of `M` along an open immersion `g` is isomorphic to a free sheaf on a finite
index type, then `M.over (image of g)` has a finite family of generating sections whose `π` is an
isomorphism. -/
theorem exists_generatingSections_of_restrict_iso_free {X Y : Scheme.{u}} (M : X.Modules) (g : Y ⟶ X)
    [IsOpenImmersion g] (ι : Type u) [Finite ι]
    (ψ : M.restrict g ≅ SheafOfModules.free (R := Y.ringCatSheaf) ι) :
    ∃ σ : (M.over g.opensRange).GeneratingSections, IsIso σ.π ∧ σ.IsFiniteType := by
  let U := g.opensRange
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (overOfOpenImmersion g).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
      (overEquiv U).inverse.mapIso (restrictUnitIso g.isoOpensRange.inv).symm
  let i : (overOfOpenImmersion g).obj (M.restrict g) ≅ M.over U :=
    (overEquiv U).inverse.mapIso
      ((restrictFunctorComp g.isoOpensRange.inv g).symm.app M ≪≫
        (restrictFunctorCongr g.isoOpensRange_inv_comp).app M ≪≫
        (overFunctorEquiv U).symm.app M) ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm
  let N : SheafOfModules.{u} Y.ringCatSheaf := M.restrict g
  let p : SheafOfModules.free (R := Y.ringCatSheaf) ι ⟶ N := ψ.inv
  have hp : IsIso p := ⟨ψ.hom, ψ.inv_hom_id, ψ.hom_inv_id⟩
  let σ0 : N.GeneratingSections :=
    (SheafOfModules.free.generatingSections (R := Y.ringCatSheaf) ι).ofEpi p
  have hfin0 : σ0.IsFiniteType := ⟨inferInstanceAs (Finite ι)⟩
  have h0 : IsIso σ0.π := by
    rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
    exact IsIso.comp_isIso' (IsIso.id _) hp
  have h1 : IsIso (σ0.map (overOfOpenImmersion g) η).π := by
    rw [SheafOfModules.GeneratingSections.map_π_eq]
    exact IsIso.comp_isIso' (Iso.isIso_hom _) (Functor.map_isIso _ _)
  have hi : IsIso i.hom := Iso.isIso_hom i
  refine ⟨(σ0.map (overOfOpenImmersion g) η).ofEpi i.hom, ?_, ⟨inferInstanceAs (Finite ι)⟩⟩
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  exact IsIso.comp_isIso' h1 hi

/-- Locally (along open immersions) isomorphic to a free sheaf of finite rank ⇒ locally free of finite
type. -/
theorem isLocallyFree_and_isFiniteType_of_restrict_free_finite {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (_ : IsOpenImmersion g) (ι : Type u) (_ : Finite ι),
      x ∈ Set.range g.base ∧ Nonempty (M.restrict g ≅ SheafOfModules.free (R := Y.ringCatSheaf) ι)) :
    M.IsLocallyFree ∧ M.IsFiniteType := by
  choose Y g hg ι hι hx hψ using h
  have hgen := fun x ↦ exists_generatingSections_of_restrict_iso_free M (g x) (ι x) (hψ x).some
  choose σ hσ hσfin using hgen
  have hc : (Opens.grothendieckTopology X).CoversTop (fun x ↦ (g x).opensRange) := by
    rw [Opens.coversTop_iff]
    exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩
  let d : SheafOfModules.LocalGeneratorsData.{u} M :=
    { I := X, X := fun x ↦ (g x).opensRange, coversTop := hc, generators := σ }
  have hd : d.IsLocallyFreeData := { isIso := hσ }
  have hd' : d.IsFiniteType := { isFiniteType := hσfin }
  exact ⟨{ exists_isLocallyFreeData := ⟨d, hd⟩ }, { exists_localGeneratorsData := ⟨d, hd'⟩ }⟩

/-- A sheaf of modules locally isomorphic to the structure sheaf satisfies the hypothesis of the
previous lemma. -/
theorem exists_restrict_free_finite_of_locally_unit {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U),
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (_ : IsOpenImmersion g) (ι : Type u) (_ : Finite ι),
      x ∈ Set.range g.base ∧ Nonempty (M.restrict g ≅ SheafOfModules.free (R := Y.ringCatSheaf) ι) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := h x
  exact ⟨U.toScheme, U.ι, inferInstance, PUnit.{u + 1}, inferInstance, by simpa using hxU,
    ⟨e ≪≫ unitIsoFreePUnit U.toScheme⟩⟩

/-- Locally isomorphic to the structure sheaf ⇒ locally free. -/
theorem isLocallyFree_of_locally_unit {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U),
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) : M.IsLocallyFree :=
  (isLocallyFree_and_isFiniteType_of_restrict_free_finite M
    (exists_restrict_free_finite_of_locally_unit M h)).1

/-- Locally isomorphic to the structure sheaf ⇒ finite type. -/
theorem isFiniteType_of_locally_unit {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U),
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) : M.IsFiniteType :=
  (isLocallyFree_and_isFiniteType_of_restrict_free_finite M
    (exists_restrict_free_finite_of_locally_unit M h)).2

end AlgebraicGeometry.Scheme.Modules

end
