import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Exterior powers commute with restriction to an open

Along an open immersion there is a canonical isomorphism between the restriction of the exterior
power of a sheaf of modules and the exterior power of the restriction.

Proof:
1. Construct the sheafification isomorphism from the pushforward along the open functor and the
   continuity of sheafification of modules.
2. On the presheaf level use the universal property of the alternating map of the exterior power
   pointwise, giving the formula for the isomorphism on objects.
3. Prove that the comparison map is an isomorphism by local bijectivity and the sheafification
   adjunction.

Source: Stacks Project, `modules.tex`; cf. `ExteriorPowerRestriction`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace MiyaokaMori.ExteriorPowerRestrictionIso

universe u

variable (X : Scheme.{u}) (U : X.Opens)

local instance exteriorRestrictionIsoCommRing {Y : Scheme.{u}} (V : Y.Opensᵒᵖ) :
    CommRing (Y.ringCatSheaf.obj.obj V) :=
  inferInstanceAs (CommRing Γ(Y, V.unop))

def openModulePresheafRestrictFunctor : X.PresheafOfModules ⥤ U.toScheme.PresheafOfModules :=
  PresheafOfModules.pushforward₀ U.ι.opensFunctor X.ringCatSheaf.obj

set_option backward.isDefEq.respectTransparency false in
def exteriorPresheafRestrictIso (M : X.PresheafOfModules) (n : ℕ) :
    (openModulePresheafRestrictFunctor X U).obj (AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf X M n) ≅
      AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf U.toScheme
        ((openModulePresheafRestrictFunctor X U).obj M) n := by
  dsimp only [openModulePresheafRestrictFunctor, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf]
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
def openModulePresheafRestrictIso (F : X.Modules) :
    (openModulePresheafRestrictFunctor X U).obj F.val ≅
      ((Scheme.Modules.restrictFunctor U.ι).obj F).val := by
  unfold Scheme.Modules.restrictFunctor
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
theorem moduleSheafificationDesc_isIso {Y : Scheme.{u}} {M : Y.PresheafOfModules}
    {F : Y.Modules} (g : M ⟶ F.val)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf _).map g)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf _).map g)] :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).symm g) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf Y.ringCatSheaf)]
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm, Adjunction.homEquiv_counit]
  have : IsIso ((presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat).map ((PresheafOfModules.toPresheaf _).map g)) :=
    ((Opens.grothendieckTopology Y).W_iff _).mp
      ((Opens.grothendieckTopology Y).W_of_isLocallyBijective _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
def openModuleSheafificationUnit (M : X.PresheafOfModules) :
    (openModulePresheafRestrictFunctor X U).obj M ⟶
      ((Scheme.Modules.restrictFunctor U.ι).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M)).val where
  app V := ModuleCat.ofHom
    (X := ((openModulePresheafRestrictFunctor X U).obj M).obj V)
    (Y := ((Scheme.Modules.restrictFunctor U.ι).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M)).val.obj V)
    { toFun := fun a ↦ ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app M).app (op (U.ι ''ᵁ V.unop)) a
      map_add' a b := map_add _ a b
      map_smul' r a := by
        change ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app M).app _ (r • a) =
          (U.ι.appIso V.unop).inv r •
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app M).app _ a
        rw [Scheme.Opens.ι_appIso]
        exact map_smul _ r a }
  naturality {V W} i := by
    ext a
    exact PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app M)
      (U.ι.opensFunctor.map i.unop).op a

set_option backward.isDefEq.respectTransparency false in
def openImmersionModuleSheafificationAbIso {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.PresheafOfModules) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (f.opensFunctor.op ⋙ M.presheaf) ≅
      (SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.restrictFunctor f).obj
          ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj M)) := by
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology Z
  let F := (SheafOfModules.toSheaf Y.ringCatSheaf).obj
    ((Scheme.Modules.restrictFunctor f).obj
      ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj M))
  let g : f.opensFunctor.op ⋙ M.presheaf ⟶ F.obj :=
    Functor.whiskerLeft f.opensFunctor.op (CategoryTheory.toSheafify K M.presheaf)
  letI : Presheaf.IsLocallyInjective J g :=
    Presheaf.isLocallyInjective_whisker J K f.opensFunctor _
  letI : Presheaf.IsLocallySurjective J g :=
    Presheaf.isLocallySurjective_whisker J K f.opensFunctor _
  letI : IsIso ((presheafToSheaf J AddCommGrpCat).map g) :=
    (J.W_iff g).mp (J.W_of_isLocallyBijective g)
  exact asIso ((presheafToSheaf J AddCommGrpCat).map g ≫
    (sheafificationAdjunction J AddCommGrpCat).counit.app F)

set_option backward.isDefEq.respectTransparency false in
theorem openImmersionModuleSheafificationAbIso_unit {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.PresheafOfModules) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
        (f.opensFunctor.op ⋙ M.presheaf) ≫
      (openImmersionModuleSheafificationAbIso f M).hom.hom =
        Functor.whiskerLeft f.opensFunctor.op
          (CategoryTheory.toSheafify (Opens.grothendieckTopology Z) M.presheaf) := by
  let F := (SheafOfModules.toSheaf Y.ringCatSheaf).obj
    ((Scheme.Modules.restrictFunctor f).obj
      ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj M))
  let g : f.opensFunctor.op ⋙ M.presheaf ⟶ F.obj :=
    Functor.whiskerLeft f.opensFunctor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Z) M.presheaf)
  exact ((sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat).homEquiv
    (f.opensFunctor.op ⋙ M.presheaf) F).apply_symm_apply g

set_option backward.isDefEq.respectTransparency false in
theorem openModuleSheafificationUnit_isLocallyBijective (M : X.PresheafOfModules) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
        ((PresheafOfModules.toPresheaf _).map (openModuleSheafificationUnit X U M)) ∧
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
        ((PresheafOfModules.toPresheaf _).map (openModuleSheafificationUnit X U M)) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) M.presheaf)) ∧
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) M.presheaf))
  exact ⟨Presheaf.isLocallyInjective_whisker _ (Opens.grothendieckTopology X) _ _,
    Presheaf.isLocallySurjective_whisker _ (Opens.grothendieckTopology X) _ _⟩

set_option backward.isDefEq.respectTransparency false in
def openModuleSheafificationMap (M : X.PresheafOfModules) :
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).obj
        ((openModulePresheafRestrictFunctor X U).obj M) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv
    (P := (openModulePresheafRestrictFunctor X U).obj M)
    (F := (Scheme.Modules.restrictFunctor U.ι).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M))
    (𝟙 U.toScheme.ringCatSheaf.obj)).symm (openModuleSheafificationUnit X U M)

set_option backward.isDefEq.respectTransparency false in
theorem openModuleSheafificationMap_isIso (M : X.PresheafOfModules) :
    IsIso (openModuleSheafificationMap X U M) := by
  have := (openModuleSheafificationUnit_isLocallyBijective X U M).1
  have := (openModuleSheafificationUnit_isLocallyBijective X U M).2
  exact moduleSheafificationDesc_isIso (Y := U.toScheme)
    (M := (openModulePresheafRestrictFunctor X U).obj M)
    (F := (Scheme.Modules.restrictFunctor U.ι).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M))
    (openModuleSheafificationUnit X U M)

set_option backward.isDefEq.respectTransparency false in
def openModuleSheafificationIso (M : X.PresheafOfModules) :
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).obj
        ((openModulePresheafRestrictFunctor X U).obj M) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M) := by
  letI := openModuleSheafificationMap_isIso X U M
  exact asIso (openModuleSheafificationMap X U M)

set_option backward.isDefEq.respectTransparency false in
def moduleExteriorPowerRestrictIso (F : X.Modules) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X F n) ≅
      AlgebraicGeometry.Scheme.Modules.moduleExteriorPower U.toScheme
        ((Scheme.Modules.restrictFunctor U.ι).obj F) n :=
  (openModuleSheafificationIso X U
      (AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf X F.val n)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (exteriorPresheafRestrictIso X U F.val n ≪≫
        (AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheafFunctor U.toScheme n).mapIso
          (openModulePresheafRestrictIso X U F))

end MiyaokaMori.ExteriorPowerRestrictionIso
