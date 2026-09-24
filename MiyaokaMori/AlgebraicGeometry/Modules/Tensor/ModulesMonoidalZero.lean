import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Whiskering with a zero morphism is zero

**Whiskering with a zero morphism is zero in `X.Modules`** (the two zero axioms of
`MonoidalPreadditive`, proved as theorems; no global instance is registered).

`X.Modules` carries the monoidal structure of `CategoryTheory.LocalizedMonoidal` (sheafification of
the objectwise tensor product of presheaves of modules). Mathlib has
`MonoidalPreadditive (ModuleCat R)` but nothing for presheaves or sheaves of modules, so `M ◁ 0 = 0`
and `0 ▷ M = 0` are derived here (named `whiskerLeft_zeroMorphism` / `zeroMorphism_whiskerRight`; cf.
`Modules.zero_whiskerRight` in `TotalSpaceHomEquivZeroSection`):

1. `Localization.Lifting.map_zero_of_lifting`: a functor `G : D ⥤ E` lifting `F : C ⥤ E` along a
   localization `L : C ⥤ D` kills zero morphisms as soon as `L` and `F` do (`L` is essentially
   surjective, `Localization.essSurj`, so every zero morphism of `D` is conjugate to `L.map 0`).
2. In `LocalizedMonoidal`, `L.obj M' ◁ g = ((tensorBifunctor).obj (L.obj M')).map g`, and that
   functor lifts `tensorLeft M' ⋙ L` (Mathlib instance). Sheafification is additive (left adjoint of
   the additive `forget ⋙ restrictScalars`), and `M' ◁ 0 = 0` for presheaves is objectwise
   `MonoidalPreadditive.whiskerLeft_zero` in `ModuleCat`.
3. For a general sheaf `M ≅ L.obj M'` (essential surjectivity), transport by `whisker_exchange`.

Source: Stacks 01CD (tensor product of sheaves of modules is additive in each variable). Used for
`dualMap 0 = 0` in the description of the total space of a line bundle over an affine base.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory.Localization

/-- A lifting `G` of `F` along a localization functor `L` kills zero morphisms if `L` and `F` do. -/
theorem Lifting.map_zero_of_lifting {C : Type u} {D : Type v} {E : Type w}
    [Category.{u'} C] [Category.{v'} D] [Category.{w'} E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] (F : C ⥤ E) (G : D ⥤ E)
    [Lifting L W F G]
    (hL : ∀ {Y Z : C}, L.map (0 : Y ⟶ Z) = 0) (hF : ∀ {Y Z : C}, F.map (0 : Y ⟶ Z) = 0)
    {Y Z : D} : G.map (0 : Y ⟶ Z) = 0 := by
  haveI := Localization.essSurj L W
  have h0 : (0 : Y ⟶ Z) = (L.objObjPreimageIso Y).inv ≫
      L.map (0 : L.objPreimage Y ⟶ L.objPreimage Z) ≫ (L.objObjPreimageIso Z).hom := by
    rw [hL, zero_comp, comp_zero]
  have hnat := (Lifting.iso L W F G).hom.naturality (0 : L.objPreimage Y ⟶ L.objPreimage Z)
  rw [Functor.comp_map, hF, comp_zero] at hnat
  have hG : G.map (L.map (0 : L.objPreimage Y ⟶ L.objPreimage Z)) = 0 := by
    have := congrArg (fun t => t ≫ (Lifting.iso L W F G).inv.app (L.objPreimage Z)) hnat
    simpa using this
  rw [h0, G.map_comp, G.map_comp, hG, zero_comp, comp_zero]

end CategoryTheory.Localization

namespace AlgebraicGeometry.Scheme.Modules

/-- Objectwise: `M ◁ 0 = 0` for presheaves of modules over a presheaf of commutative rings
(`MonoidalPreadditive.whiskerLeft_zero` in `ModuleCat`, applied at every object). -/
theorem presheaf_whiskerLeft_zero {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : _root_.PresheafOfModules.{u} (R ⋙ CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u}))
    {Y Z : _root_.PresheafOfModules.{u} (R ⋙ CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})} :
    M ◁ (0 : Y ⟶ Z) = 0 := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  rw [_root_.PresheafOfModules.whiskerLeft_app, _root_.PresheafOfModules.zero_app,
    _root_.PresheafOfModules.zero_app]
  exact MonoidalPreadditive.whiskerLeft_zero

/-- Objectwise: `0 ▷ M = 0` for presheaves of modules over a presheaf of commutative rings. -/
theorem presheaf_zero_whiskerRight {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : _root_.PresheafOfModules.{u} (R ⋙ CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u}))
    {Y Z : _root_.PresheafOfModules.{u} (R ⋙ CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})} :
    (0 : Y ⟶ Z) ▷ M = 0 := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  rw [_root_.PresheafOfModules.whiskerRight_app, _root_.PresheafOfModules.zero_app,
    _root_.PresheafOfModules.zero_app]
  exact MonoidalPreadditive.zero_whiskerRight

/-- Sheafification of presheaves of modules kills zero morphisms (it is a left adjoint of an
additive functor). -/
theorem sheafification_map_zero (X : AlgebraicGeometry.Scheme.{u})
    {Y Z : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj} : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (0 : Y ⟶ Z) = 0 := by
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Additive :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_adjoint_additive
  exact Functor.map_zero _ _ _

/-- `M ◁ 0 = 0` for a sheafified presheaf. -/
theorem sheafification_obj_whiskerLeft_zero (X : AlgebraicGeometry.Scheme.{u})
    (M' : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) {Y Z : X.Modules} :
    (show X.Modules from (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M') ◁
      (0 : Y ⟶ Z) = 0 := by
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  letI : HasZeroMorphisms (CategoryTheory.LocalizedMonoidal (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)) :=
    inferInstanceAs (HasZeroMorphisms (SheafOfModules.{u} X.ringCatSheaf))
  have hL : ∀ {Y Z : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj},
      (Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
        (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).map (0 : Y ⟶ Z) = 0 :=
    fun {_ _} => sheafification_map_zero X
  have hF : ∀ {Y Z : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj},
      (tensorLeft M' ⋙ Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
        (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).map (0 : Y ⟶ Z) = 0 := by
    intro Y Z
    show (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (M' ◁ (0 : Y ⟶ Z)) = 0
    erw [presheaf_whiskerLeft_zero (R := X.presheaf)]
    exact sheafification_map_zero X
  exact Localization.Lifting.map_zero_of_lifting
    (Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
    (tensorLeft M' ⋙ Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X))
    ((Localization.Monoidal.tensorBifunctor (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).obj
        ((Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
          (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).obj M'))
    hL hF

/-- `0 ▷ M = 0` for a sheafified presheaf. -/
theorem zero_whiskerRight_sheafification_obj (X : AlgebraicGeometry.Scheme.{u})
    (M' : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) {Y Z : X.Modules} :
    (0 : Y ⟶ Z) ▷
      (show X.Modules from (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M') = 0 := by
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  letI : HasZeroMorphisms (CategoryTheory.LocalizedMonoidal (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)) :=
    inferInstanceAs (HasZeroMorphisms (SheafOfModules.{u} X.ringCatSheaf))
  have hL : ∀ {Y Z : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj},
      (Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
        (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).map (0 : Y ⟶ Z) = 0 :=
    fun {_ _} => sheafification_map_zero X
  have hF : ∀ {Y Z : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj},
      (tensorRight M' ⋙ Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
        (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).map (0 : Y ⟶ Z) = 0 := by
    intro Y Z
    show (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ((0 : Y ⟶ Z) ▷ M') = 0
    erw [presheaf_zero_whiskerRight (R := X.presheaf)]
    exact sheafification_map_zero X
  exact Localization.Lifting.map_zero_of_lifting
    (Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
    (tensorRight M' ⋙ Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X))
    ((Localization.Monoidal.tensorBifunctor (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).flip.obj
        ((Localization.Monoidal.toMonoidalCategory (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
          (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)).obj M'))
    hL hF

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **`M ◁ 0 = 0` in `X.Modules`** (`MonoidalPreadditive.whiskerLeft_zero`, as a theorem). -/
theorem whiskerLeft_zeroMorphism (M : X.Modules) {Y Z : X.Modules} : M ◁ (0 : Y ⟶ Z) = 0 := by
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  haveI := Localization.essSurj (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
  let e : (show X.Modules from (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).objPreimage M)) ≅ M :=
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).objObjPreimageIso M
  calc M ◁ (0 : Y ⟶ Z) = (M ◁ (0 : Y ⟶ Z)) ≫ ((e.inv ▷ Z) ≫ (e.hom ▷ Z)) := by
        rw [← comp_whiskerRight, e.inv_hom_id, id_whiskerRight, Category.comp_id]
    _ = ((e.inv ▷ Y) ≫ ((show X.Modules from (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
          ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).objPreimage M)) ◁ (0 : Y ⟶ Z))) ≫
          (e.hom ▷ Z) := by
        rw [← Category.assoc, ← whisker_exchange]
    _ = 0 := by
        rw [sheafification_obj_whiskerLeft_zero, comp_zero, zero_comp]

/-- **`0 ▷ M = 0` in `X.Modules`** (`MonoidalPreadditive.zero_whiskerRight`, as a theorem). -/
theorem zeroMorphism_whiskerRight (M : X.Modules) {Y Z : X.Modules} : (0 : Y ⟶ Z) ▷ M = 0 := by
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  haveI := Localization.essSurj (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
  let e : (show X.Modules from (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).objPreimage M)) ≅ M :=
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).objObjPreimageIso M
  calc (0 : Y ⟶ Z) ▷ M = ((Y ◁ e.inv) ≫ (Y ◁ e.hom)) ≫ ((0 : Y ⟶ Z) ▷ M) := by
        rw [← whiskerLeft_comp, e.inv_hom_id, whiskerLeft_id, Category.id_comp]
    _ = (Y ◁ e.inv) ≫ (((0 : Y ⟶ Z) ▷ (show X.Modules from (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
          ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).objPreimage M))) ≫ (Z ◁ e.hom)) := by
        rw [Category.assoc, whisker_exchange]
    _ = 0 := by
        rw [zero_whiskerRight_sheafification_obj, zero_comp, comp_zero]

/-- `f ⊗ₘ 0 = 0` in `X.Modules`. -/
theorem tensorHom_zeroMorphism {M N Y Z : X.Modules} (f : M ⟶ N) : f ⊗ₘ (0 : Y ⟶ Z) = 0 := by
  rw [tensorHom_def, whiskerLeft_zeroMorphism, comp_zero]

/-- `0 ⊗ₘ g = 0` in `X.Modules`. -/
theorem zeroMorphism_tensorHom {M N Y Z : X.Modules} (g : Y ⟶ Z) : (0 : M ⟶ N) ⊗ₘ g = 0 := by
  rw [tensorHom_def, zeroMorphism_whiskerRight, zero_comp]

end AlgebraicGeometry.Scheme.Modules

end
