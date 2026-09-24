import MiyaokaMori.Prelude
import Mathlib.Topology.Sheaves.Abelian
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor

/-! # Exactness of the stalk functor on sheaves of modules

The stalk functor on `O_X`-modules is exact: the stalk of the kernel or cokernel of a morphism is
the kernel or cokernel of the stalk map (`F ↦ F_x` preserves finite limits and all colimits).

Source: Stacks 01AJ, 007Z (the stalk functor is exact).

Proof sketch. Write `F := Scheme.Modules.stalkFunctor x` and `G := forget₂ (ModuleCat O_{X,x}) Ab`.
1. `F ⋙ G` agrees on objects and morphisms with
   `SheafOfModules.toSheaf X.ringCatSheaf ⋙ (TopCat.Sheaf.forget Ab X ⋙ TopCat.Presheaf.stalkFunctor Ab x)`
   (`stalkFunctor_comp_forget₂_iso`, all components `Iso.refl`).
2. `toSheaf` preserves finite limits (Mathlib instance, `Algebra/Category/ModuleCat/Sheaf/Limits.lean`)
   and all small colimits (`toSheaf_preservesColimits`: by `Adjunction.preservesColimitsOfSize_iff` for
   the sheafification adjunction `PresheafOfModules.sheafificationAdjunction`, reduce to
   `sheafification ⋙ toSheaf ≅ toPresheaf ⋙ presheafToSheaf`, a forgetful functor computing colimits
   objectwise followed by a left adjoint).
3. `TopCat.Sheaf.forget Ab X ⋙ stalkFunctor Ab x` preserves finite limits (Mathlib
   `Topology/Sheaves/Abelian.lean`: stalks are filtered colimits, which commute with finite limits in
   `Ab`) and is a left adjoint (skyscraper adjunction, `Topology/Sheaves/Skyscraper.lean`), hence
   preserves all colimits.
4. `G` reflects finite limits and colimits (Mathlib `ModuleCat/Limits.lean`, `ModuleCat/Colimits.lean`);
   conclude with `preservesFiniteLimits_of_reflects_of_preserves` / `preservesColimits_of_reflects_of_preserves`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The stalk functor followed by the forgetful functor to `Ab` is "underlying abelian sheaf ↦ its
stalk at `x`" (equal on objects and on morphisms). -/
def AlgebraicGeometry.Scheme.Modules.stalkFunctor_comp_forget₂_iso
    {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    AlgebraicGeometry.Scheme.Modules.stalkFunctor x ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf :
          X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
  NatIso.ofComponents (fun M => Iso.refl _) (fun f => by
    ext m
    rfl)

/-- `toSheaf : X.Modules ⥤ Sheaf Ab` preserves all small colimits: by the sheafification adjunction
this reduces to `sheafification ⋙ toSheaf ≅ toPresheaf ⋙ presheafToSheaf`. -/
theorem AlgebraicGeometry.Scheme.Modules.toSheaf_preservesColimits (X : AlgebraicGeometry.Scheme.{u}) :
    PreservesColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := by
  have h1 : PreservesColimitsOfSize.{u, u}
      (PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj) := ⟨fun {_} _ => inferInstance⟩
  apply ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).preservesColimitsOfSize_iff
    (H := SheafOfModules.toSheaf.{u} X.ringCatSheaf)).mpr
  exact preservesColimits_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 X.ringCatSheaf.obj)).symm

/-- The stalk functor `X.Modules ⥤ ModuleCat O_{X,x}` preserves finite limits and all colimits. -/
theorem AlgebraicGeometry.Scheme.Modules.stalk_preservesFiniteLimits_colimits {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    CategoryTheory.Limits.PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) ∧
      CategoryTheory.Limits.PreservesColimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) := by
  let G := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have e := AlgebraicGeometry.Scheme.Modules.stalkFunctor_comp_forget₂_iso x
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let T : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have hS1 : PreservesFiniteLimits S := inferInstance
  have hS2 : PreservesColimits S := inferInstance
  have hT1 : PreservesFiniteLimits T :=
    (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  have hT2 : PreservesColimits T := AlgebraicGeometry.Scheme.Modules.toSheaf_preservesColimits X
  have hG1 : ReflectsFiniteLimits G := inferInstance
  have hG2 : ReflectsColimits G := ⟨fun {_} _ => inferInstance⟩
  have hTS1 : PreservesFiniteLimits (T ⋙ S) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ T S hT1 hS1
  have hTS2 : PreservesColimits (T ⋙ S) :=
    @comp_preservesColimits _ _ _ _ _ _ T S hT2 hS2
  have hFG1 : PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x ⋙ G) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ e.symm hTS1
  have hFG2 : PreservesColimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x ⋙ G) :=
    @preservesColimits_of_natIso _ _ _ _ _ _ e.symm hTS2
  exact ⟨@preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _
      (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) G hFG1 hG1,
    @preservesColimits_of_reflects_of_preserves _ _ _ _ _ _
      (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) G hFG2 hG2⟩

end
