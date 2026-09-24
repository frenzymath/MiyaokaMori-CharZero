import MiyaokaMori.Prelude

/-! # Local freeness is detected on a cover by open immersions

If every point of `X` lies in the image of some open immersion `g : Y ⟶ X` along which `M` restricts
to a free sheaf, then `M` is locally free.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- `Y`-modules → `X.ringCatSheaf.over (image of g)`-modules: restrict along `image ≅ Y`, then apply
`overEquiv`. -/
private def restrictFreeCover.overF {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} (X.ringCatSheaf.over g.opensRange) :=
  Scheme.Modules.restrictFunctor g.isoOpensRange.inv ⋙ (Scheme.Modules.overEquiv g.opensRange).inverse

private instance restrictFreeCover.overF_pres {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    PreservesColimitsOfSize.{u, u} (restrictFreeCover.overF g) := by
  have h1 : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor g.isoOpensRange.inv) :=
    inferInstance
  have h2 : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv g.opensRange).inverse :=
    inferInstance
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h1 h2

/-- If the restriction of `M` along an open immersion `g` is free, then `M.over (image of g)` has a
family of generating sections whose `π` is an isomorphism. -/
private theorem restrictFreeCover.over_gen {X Y : Scheme.{u}} (M : X.Modules) (g : Y ⟶ X)
    [IsOpenImmersion g] (ι : Type u)
    (ψ : M.restrict g ≅ SheafOfModules.free (R := Y.ringCatSheaf) ι) :
    ∃ σ : (M.over g.opensRange).GeneratingSections, IsIso σ.π := by
  let U := g.opensRange
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (restrictFreeCover.overF g).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
      (Scheme.Modules.overEquiv U).inverse.mapIso
        (Scheme.Modules.restrictUnitIso g.isoOpensRange.inv).symm
  let i : (restrictFreeCover.overF g).obj (M.restrict g) ≅ M.over U :=
    (Scheme.Modules.overEquiv U).inverse.mapIso
      ((Scheme.Modules.restrictFunctorComp g.isoOpensRange.inv g).symm.app M ≪≫
        (Scheme.Modules.restrictFunctorCongr g.isoOpensRange_inv_comp).app M ≪≫
        (Scheme.Modules.overFunctorEquiv U).symm.app M) ≪≫
      ((Scheme.Modules.overEquiv U).unitIso.app (M.over U)).symm
  let N : SheafOfModules.{u} Y.ringCatSheaf := M.restrict g
  let p : SheafOfModules.free (R := Y.ringCatSheaf) ι ⟶ N := ψ.inv
  have hp : IsIso p := ⟨ψ.hom, ψ.inv_hom_id, ψ.hom_inv_id⟩
  let σ0 : N.GeneratingSections :=
    (SheafOfModules.free.generatingSections (R := Y.ringCatSheaf) ι).ofEpi p
  have h0 : IsIso σ0.π := by
    rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
    exact IsIso.comp_isIso' (IsIso.id _) hp
  have h1 : IsIso (σ0.map (restrictFreeCover.overF g) η).π := by
    rw [SheafOfModules.GeneratingSections.map_π_eq]
    exact IsIso.comp_isIso' (Iso.isIso_hom _) (Functor.map_isIso _ _)
  have hi : IsIso i.hom := Iso.isIso_hom i
  refine ⟨(σ0.map (restrictFreeCover.overF g) η).ofEpi i.hom, ?_⟩
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  exact IsIso.comp_isIso' h1 hi

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_restrict_free {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules)
    (h : ∀ x : X, ∃ (Y : AlgebraicGeometry.Scheme.{u}) (g : Y ⟶ X) (_ : AlgebraicGeometry.IsOpenImmersion g)
      (ι : Type u), x ∈ Set.range g.base ∧
        Nonempty (M.restrict g ≅ SheafOfModules.free (R := Y.ringCatSheaf) ι)) :
    M.IsLocallyFree := by
  choose Y g hg ι hx hψ using h
  have hgen := fun x => restrictFreeCover.over_gen M (g x) (ι x) (hψ x).some
  choose σ hσ using hgen
  have hc : (Opens.grothendieckTopology X).CoversTop (fun x => (g x).opensRange) := by
    rw [Opens.coversTop_iff]
    exact eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩
  let d : SheafOfModules.LocalGeneratorsData.{u} M :=
    { I := X, X := fun x => (g x).opensRange, coversTop := hc, generators := σ }
  have hd : d.IsLocallyFreeData := { isIso := hσ }
  exact { exists_isLocallyFreeData := ⟨d, hd⟩ }

end
