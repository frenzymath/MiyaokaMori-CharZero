import MiyaokaMori.Prelude
import MiyaokaMori.CategoryTheory.PresheafModulesTensorLocallySurjective
import MiyaokaMori.CategoryTheory.PresheafModulesTensorLocallyInjective

/-! # The tensor product of presheaves of modules preserves local isomorphisms

On a scheme, the tensor product of presheaves of modules preserves the morphisms that become
isomorphisms after sheafification: this class `W` is monoidal (`W.IsMonoidal`), so sheafification
transports the presheaf tensor product to a monoidal structure on sheaves of modules.

Source: Stacks 01CA (stalks of the tensor product). This is the essential input for the monoidal
structure on `X.Modules`.

Proof (without stalks): a morphism becomes an isomorphism after sheafification iff its underlying
morphism of presheaves of abelian groups lies in `J.W` (Mathlib
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`) iff it is locally
injective and locally surjective (`J.W_iff_isLocallyBijective`); if `f` is locally bijective then
`f ▷ P` is locally surjective (`PresheafModulesTensorLocallySurjective`) and locally injective
(`PresheafModulesTensorLocallyInjective`, via the vanishing criterion for tensor products); left
whiskering reduces to right whiskering through the braiding.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open MonoidalCategory in
/-- Version on a general site: among presheaves of modules over a presheaf of commutative rings `R`,
the class of morphisms whose underlying morphism of presheaves of abelian groups lies in `J.W` (i.e.
the locally bijective ones) is closed under tensor product. Right whiskering follows from
`PresheafOfModules.isLocallySurjective_whiskerRight` and
`PresheafOfModules.isLocallyInjective_whiskerRight`; left whiskering reduces to right whiskering via
the braiding `β`. -/
theorem PresheafOfModules.W_inverseImage_toPresheaf_isMonoidal
    {C : Type*} [Category* C] (J : GrothendieckTopology C) [J.WEqualsLocallyBijective Ab.{u}]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    (J.W.inverseImage (_root_.PresheafOfModules.toPresheaf.{u}
      (R ⋙ CategoryTheory.forget₂ CommRingCat RingCat))).IsMonoidal := by
  have hR : ∀ {M N : _root_.PresheafOfModules.{u} (R ⋙ CategoryTheory.forget₂ CommRingCat RingCat)}
      (f : M ⟶ N) (_ : (J.W.inverseImage (_root_.PresheafOfModules.toPresheaf _)) f)
      (P : _root_.PresheafOfModules.{u} (R ⋙ CategoryTheory.forget₂ CommRingCat RingCat)),
      (J.W.inverseImage (_root_.PresheafOfModules.toPresheaf _)) (f ▷ P) := by
    intro M N f hf P
    obtain ⟨h₁, h₂⟩ := (J.W_iff_isLocallyBijective _).1 hf
    have := _root_.PresheafOfModules.isLocallySurjective_whiskerRight J f P
    have := _root_.PresheafOfModules.isLocallyInjective_whiskerRight J f P
    exact J.W_of_isLocallyBijective _
  exact
    { whiskerRight := fun f hf P ↦ hR f hf P
      whiskerLeft := fun P _ _ g hg ↦
        ((J.W.inverseImage (_root_.PresheafOfModules.toPresheaf _)).arrow_mk_iso_iff
          (Arrow.isoMk (β_ P _) (β_ P _))).2 (hR g hg P) }

/-- The monoidal structure on presheaves of modules, transported to `X.ringCatSheaf.obj` (which is
definitionally `X.presheaf ⋙ forget₂`; Mathlib's instance only recognizes the latter spelling). -/

noncomputable instance AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (CategoryTheory.MonoidalCategory
    (_root_.PresheafOfModules.{u} (X.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat)))

/-- On a scheme, the class of morphisms of presheaves of modules that become isomorphisms after
sheafification is monoidal. -/
theorem AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal (X : AlgebraicGeometry.Scheme.{u}) :
    ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))).IsMonoidal := by
  rw [← _root_.PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)]
  exact _root_.PresheafOfModules.W_inverseImage_toPresheaf_isMonoidal
    (Opens.grothendieckTopology X) X.presheaf

end
