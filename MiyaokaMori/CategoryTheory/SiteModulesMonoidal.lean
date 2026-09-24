import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso

/-! # The symmetric monoidal structure on sheaves of modules over a site

Let `J` be a Grothendieck topology on a category `C` and `R : Sheaf J CommRingCat` a sheaf of
commutative rings. The symmetric monoidal structure on presheaves of modules
`PresheafOfModules (R ⋙ forget₂)` is pushed down along sheafification to a symmetric monoidal
structure on `SheafOfModules (ringCatSheafOfComm R)`.

The case of a scheme `X` (the monoidal structure on `X.Modules`, `SheafOfModulesMonoidal`) is a special
case. The construction is made over a general site because the definition of quasi-coherence
(Mathlib `SheafOfModules.QuasicoherentData`) takes presentations over the **slice site** `J.over U`,
where a monoidal structure is needed as well.

The only substantial input is `PresheafOfModules.W_inverseImage_toPresheaf_isMonoidal`
(`PresheafModulesTensorLocalIso`), which is proved for a general site.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace SiteModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})]

/-- The `RingCat`-valued sheaf of rings underlying a sheaf of commutative rings `R`. For a scheme `X`,
`ringCatSheafOfComm X.sheaf` **is** `X.ringCatSheaf` (`rfl`). -/
abbrev ringCatSheafOfComm (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- The monoidal structure on presheaves of modules transported to `(ringCatSheafOfComm R).obj`
(definitionally `R.obj ⋙ forget₂`; Mathlib's instance is stated only for the latter spelling). -/
instance presheafMonoidalCategory (R : Sheaf J CommRingCat.{u}) :
    CategoryTheory.MonoidalCategory (_root_.PresheafOfModules.{u} (ringCatSheafOfComm R).obj) :=
  inferInstanceAs (CategoryTheory.MonoidalCategory
    (_root_.PresheafOfModules.{u} (R.obj ⋙ CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})))

instance presheafSymmetricCategory (R : Sheaf J CommRingCat.{u}) :
    CategoryTheory.SymmetricCategory (_root_.PresheafOfModules.{u} (ringCatSheafOfComm R).obj) :=
  inferInstanceAs (CategoryTheory.SymmetricCategory
    (_root_.PresheafOfModules.{u} (R.obj ⋙ CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})))

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The class of morphisms that become isomorphisms after sheafification is monoidal. -/
theorem sheafificationW_isMonoidal (R : Sheaf J CommRingCat.{u}) :
    ((CategoryTheory.MorphismProperty.isomorphisms
        (SheafOfModules.{u} (ringCatSheafOfComm R))).inverseImage
      (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj))).IsMonoidal := by
  rw [← _root_.PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (ringCatSheafOfComm R).obj)]
  exact _root_.PresheafOfModules.W_inverseImage_toPresheaf_isMonoidal J R.obj

/-- The sheafification of the unit presheaf of modules (the structure presheaf) is the structure sheaf. -/
def sheafificationUnitIso (R : Sheaf J CommRingCat.{u}) :
    (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj)).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorUnit
          (_root_.PresheafOfModules.{u} (ringCatSheafOfComm R).obj)) ≅
      SheafOfModules.unit (ringCatSheafOfComm R) :=
  (CategoryTheory.asIso
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOfComm R).obj)).counit).app
    (SheafOfModules.unit (ringCatSheafOfComm R))

/-- Sheafification is a localization (with respect to `sheafificationW`). -/
theorem sheafification_isLocalization (R : Sheaf J CommRingCat.{u}) :
    (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms
          (SheafOfModules.{u} (ringCatSheafOfComm R))).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj))) :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOfComm R).obj)).isLocalization

/-- **The monoidal structure on sheaves of modules over an arbitrary site.** -/
instance monoidalCategory (R : Sheaf J CommRingCat.{u}) :
    CategoryTheory.MonoidalCategory (SheafOfModules.{u} (ringCatSheafOfComm R)) :=
  haveI := sheafificationW_isMonoidal R
  haveI := sheafification_isLocalization R
  inferInstanceAs (CategoryTheory.MonoidalCategory (CategoryTheory.LocalizedMonoidal
    (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj))
    ((CategoryTheory.MorphismProperty.isomorphisms
        (SheafOfModules.{u} (ringCatSheafOfComm R))).inverseImage
      (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj)))
    (sheafificationUnitIso R)))

/-- **The symmetric structure on sheaves of modules over an arbitrary site.** -/
instance symmetricCategory (R : Sheaf J CommRingCat.{u}) :
    CategoryTheory.SymmetricCategory (SheafOfModules.{u} (ringCatSheafOfComm R)) :=
  haveI := sheafificationW_isMonoidal R
  haveI := sheafification_isLocalization R
  inferInstanceAs (CategoryTheory.SymmetricCategory (CategoryTheory.LocalizedMonoidal
    (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj))
    ((CategoryTheory.MorphismProperty.isomorphisms
        (SheafOfModules.{u} (ringCatSheafOfComm R))).inverseImage
      (_root_.PresheafOfModules.sheafification (𝟙 (ringCatSheafOfComm R).obj)))
    (sheafificationUnitIso R)))

end SiteModules

end
