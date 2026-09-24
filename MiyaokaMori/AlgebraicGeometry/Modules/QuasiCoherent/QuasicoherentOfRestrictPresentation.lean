import MiyaokaMori.Prelude

/-! # Quasi-coherence from presentations of restrictions

Let `X` be a scheme and `M` an `O_X`-module. If every point of `X` lies in the image of some open
immersion `g : Y ⟶ X` such that the restriction `M.restrict g` has a global presentation
(`Presentation`: a cokernel of a morphism between free sheaves), then `M` is quasi-coherent. In
particular the condition holds when `M.restrict g` is isomorphic to some `tilde`.

Proof:
1. Let `U` be the image of `g`. The functor `F = (restriction along U ≅ Y) ⋙ (U-modules ≃ modules over
   X.ringCatSheaf.over U, the inverse of Mathlib's Scheme.Modules.overEquiv)` is a composite of
   equivalences, preserves colimits and sends the structure sheaf to the structure sheaf
   (`restrictUnitIso`, `sheafOfModulesEquivOverInverseUnit`); `F(M.restrict g) ≅ M.over U`
   (`restrictFunctorComp`, `isoOpensRange_inv_comp`, `overFunctorEquiv`, the unit of the equivalence).
2. `Presentation.map` transports the presentation of `M.restrict g` to `F(M.restrict g)`, and
   `Presentation.ofIsIso` to `M.over U`.
3. The `U` cover `X` (`Opens.coversTop_iff`); assemble a `QuasicoherentData`, i.e. `M` is quasi-coherent.

Source: quasi-coherence (Stacks 01BE) is local for open covers.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

private def restrictPresentation.overF {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} (X.ringCatSheaf.over g.opensRange) :=
  Scheme.Modules.restrictFunctor g.isoOpensRange.inv ⋙ (Scheme.Modules.overEquiv g.opensRange).inverse

private instance restrictPresentation.overF_pres {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    PreservesColimitsOfSize.{u, u} (restrictPresentation.overF g) := by
  have h1 : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor g.isoOpensRange.inv) :=
    inferInstance
  have h2 : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv g.opensRange).inverse :=
    inferInstance
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h1 h2

private def restrictPresentation.over_presentation {X Y : Scheme.{u}} (M : X.Modules) (g : Y ⟶ X)
    [IsOpenImmersion g] (P : SheafOfModules.Presentation.{u} (M.restrict g)) :
    SheafOfModules.Presentation.{u} (M.over g.opensRange) :=
  let U := g.opensRange
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (restrictPresentation.overF g).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
      (Scheme.Modules.overEquiv U).inverse.mapIso
        (Scheme.Modules.restrictUnitIso g.isoOpensRange.inv).symm
  let i : (restrictPresentation.overF g).obj (M.restrict g) ≅ M.over U :=
    (Scheme.Modules.overEquiv U).inverse.mapIso
      ((Scheme.Modules.restrictFunctorComp g.isoOpensRange.inv g).symm.app M ≪≫
        (Scheme.Modules.restrictFunctorCongr g.isoOpensRange_inv_comp).app M ≪≫
        (Scheme.Modules.overFunctorEquiv U).symm.app M) ≪≫
      ((Scheme.Modules.overEquiv U).unitIso.app (M.over U)).symm
  (P.map (restrictPresentation.overF g) η).ofIsIso i.hom

/-- `M` is quasi-coherent if its restrictions along a family of open immersions covering `X` have
global presentations. -/
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_restrict_presentation
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (Y : AlgebraicGeometry.Scheme.{u}) (g : Y ⟶ X) (_ : AlgebraicGeometry.IsOpenImmersion g),
      x ∈ Set.range g.base ∧ Nonempty (SheafOfModules.Presentation.{u} (M.restrict g))) :
    M.IsQuasicoherent := by
  choose Y g hg hx hP using h
  have hc : (Opens.grothendieckTopology X).CoversTop (fun x => (g x).opensRange) := by
    rw [Opens.coversTop_iff]
    exact eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩
  let d : SheafOfModules.QuasicoherentData.{u} (R := X.ringCatSheaf) M :=
    { I := X, X := fun x => (g x).opensRange, coversTop := hc
      presentation := fun x => restrictPresentation.over_presentation M (g x) (hP x).some }
  exact d.isQuasicoherent

end
