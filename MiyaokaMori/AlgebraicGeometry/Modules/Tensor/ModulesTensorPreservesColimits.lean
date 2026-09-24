import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso

/-! # The tensor product of sheaves of modules preserves colimits

The tensor product of sheaves of modules on a scheme `X` preserves colimits in each variable:
`M ⊗ -` and `- ⊗ M` (for the localized monoidal structure on `X.Modules`) are
`PreservesColimitsOfSize.{u, u}`; in particular the tensor product preserves epimorphisms and
coproducts.

Proof: the monoidal structure on `X.Modules` is the localization along sheafification `L` of the
monoidal structure on presheaves of modules. Mathlib provides
1. `Q ⊗ -` preserves colimits on presheaves of modules (the tensor product of `PresheafOfModules` is
   computed openwise, and the tensor product in `ModuleCat` is a left adjoint);
2. the comparison `μ : L P ⊗ L Q ≅ L (P ⊗ Q)` of the localized monoidal structure, natural in both
   variables;
3. `L` is a left adjoint (preserves colimits) and the counit of `L ⊣ G` is an isomorphism (`G` is
   fully faithful), so every diagram `D : K ⥤ X.Modules` is isomorphic to `(D ⋙ G) ⋙ L` and every
   object `N` to `L (G N)`.
Turn (2) into a natural isomorphism `L ⋙ (L Q ⊗ -) ≅ (Q ⊗ -) ⋙ L` (`compTensorLeftIso`) and transport
the colimit cocone of `D ⋙ G` in presheaves of modules along both paths: `L Q ⊗ -` preserves the
colimit of `(D ⋙ G) ⋙ L`; the two isomorphisms of (3) transfer this to general `D` and `N`. The
right-hand version follows from the braiding `tensorLeft N ≅ tensorRight N`.

Source: the categorical form of "the tensor product is right exact" used in Stacks 01CA/01CE; Mathlib
`CategoryTheory/Localization/Monoidal/Basic.lean` (`Localization.Monoidal.μ`),
`Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` (`tensorLeft` on presheaves of modules preserves
colimits).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

section Abstract

open CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] (L : C ⥤ D)
  (W : MorphismProperty C) [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

/-- The comparison isomorphism of the monoidal localization as a natural isomorphism of functors
`L ⋙ (L P ⊗ -) ≅ (P ⊗ -) ⋙ L`; the components are `Localization.Monoidal.μ`, naturality is
`μ_natural_right`. -/
def CategoryTheory.Localization.Monoidal.compTensorLeftIso (P : C) :
    (toMonoidalCategory L W ε) ⋙ tensorLeft ((toMonoidalCategory L W ε).obj P) ≅
      tensorLeft P ⋙ (toMonoidalCategory L W ε) :=
  NatIso.ofComponents (fun Q => μ L W ε P Q) (fun {_ _} g => μ_natural_right L W ε P g)

end Abstract

/-- Transporting a coproduct cocone along termwise isomorphisms: if `c` is a coproduct cocone of
`X : β → C` and `w b : Y b ≅ X b`, then precomposing the injections with `w b` gives a coproduct cocone
of `Y`. -/
def CategoryTheory.Limits.cofanIsColimitOfObjIso {C : Type*} [Category* C] {β : Type*}
    {Y X : β → C} (c : Cofan X) (hc : IsColimit c) (w : ∀ b, Y b ≅ X b) :
    IsColimit (Cofan.mk c.pt fun b => (w b).hom ≫ c.inj b) :=
  Cofan.IsColimit.mk _
    (fun t => hc.desc (Cofan.mk t.pt fun b => (w b).inv ≫ t.inj b))
    (fun t b => by simp)
    (fun t m hm => Cofan.IsColimit.hom_ext hc _ _ (fun b => by
      have h1 : (w b).hom ≫ c.inj b ≫ m = t.inj b := by
        simpa using hm b
      simp only [Cofan.IsColimit.inj_desc]
      show c.inj b ≫ m = (w b).inv ≫ t.inj b
      rw [← h1, Iso.inv_hom_id_assoc]))

namespace AlgebraicGeometry.Scheme.Modules

variable (X : AlgebraicGeometry.Scheme.{u})

/-- The class of morphisms inverted by sheafification (the `W` of the monoidal localization). -/
abbrev sheafificationW : MorphismProperty (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  (MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))

instance sheafificationW_isMonoidal' : (sheafificationW X).IsMonoidal :=
  AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X

instance sheafification_isLocalization :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (sheafificationW X) :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization

/-- Sheafification, as a functor into `X.Modules`. -/
abbrev sheafificationToModules :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The right adjoint of sheafification (forgetting to presheaves of modules). -/
abbrev forgetToPresheafModules :
    X.Modules ⥤ _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)

/-- `Q ⊗ -` preserves colimits on presheaves of modules (Mathlib instance, spelled for
`X.ringCatSheaf.obj`). -/
instance presheafTensorLeft_preservesColimits
    (Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorLeft Q) := by
  let Q' : _root_.PresheafOfModules.{u}
      (X.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat) := Q
  exact inferInstanceAs (PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorLeft Q'))

variable {X}

/-- `N ⊗ -` preserves colimits. -/
instance tensorLeft_preservesColimitsOfSize (N : X.Modules) :
    PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorLeft N) := by
  have hL : PreservesColimitsOfSize.{u, u} (sheafificationToModules X) :=
    Adjunction.leftAdjoint_preservesColimits
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj))
  have ci := asIso (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit
  refine ⟨?_⟩
  intro K _
  refine ⟨?_⟩
  intro Dg
  let Qn : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
    (forgetToPresheafModules X).obj N
  have eN : (sheafificationToModules X).obj Qn ≅ N := ci.app N
  have eD : (Dg ⋙ forgetToPresheafModules X) ⋙ sheafificationToModules X ≅ Dg :=
    Functor.isoWhiskerLeft Dg ci
  have α : (sheafificationToModules X) ⋙
      MonoidalCategory.tensorLeft ((sheafificationToModules X).obj Qn) ≅
      MonoidalCategory.tensorLeft Qn ⋙ (sheafificationToModules X) :=
    CategoryTheory.Localization.Monoidal.compTensorLeftIso
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (sheafificationW X)
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X) Qn
  have key : PreservesColimit
      ((Dg ⋙ forgetToPresheafModules X) ⋙ sheafificationToModules X)
      (MonoidalCategory.tensorLeft ((sheafificationToModules X).obj Qn)) := by
    refine preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (sheafificationToModules X)
        (colimit.isColimit (Dg ⋙ forgetToPresheafModules X))) ?_
    exact IsColimit.mapCoconeEquiv α.symm
      (isColimitOfPreserves (MonoidalCategory.tensorLeft Qn ⋙ sheafificationToModules X)
        (colimit.isColimit (Dg ⋙ forgetToPresheafModules X)))
  have key2 : PreservesColimit Dg
      (MonoidalCategory.tensorLeft ((sheafificationToModules X).obj Qn)) :=
    preservesColimit_of_iso_diagram _ eD
  exact preservesColimit_of_natIso Dg ((tensoringLeft X.Modules).mapIso eN)

/-- `- ⊗ N` preserves colimits (reduced to the left-hand version by the braiding). -/
instance tensorRight_preservesColimitsOfSize (N : X.Modules) :
    PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorRight N) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)

/-- The tensor product preserves epimorphisms (`Epi f ↔ IsPushout f f 𝟙 𝟙`, and `N ⊗ -` preserves
colimits). -/
instance tensorLeft_preservesEpimorphisms (N : X.Modules) :
    (MonoidalCategory.tensorLeft N).PreservesEpimorphisms where
  preserves f hf := by
    have : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft N) :=
      preservesColimitsOfSize_shrink _
    rw [epi_iff_isPushout] at hf ⊢
    simpa using hf.map (MonoidalCategory.tensorLeft N)

instance tensorRight_preservesEpimorphisms (N : X.Modules) :
    (MonoidalCategory.tensorRight N).PreservesEpimorphisms where
  preserves f hf := by
    have : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight N) :=
      preservesColimitsOfSize_shrink _
    rw [epi_iff_isPushout] at hf ⊢
    simpa using hf.map (MonoidalCategory.tensorRight N)

end AlgebraicGeometry.Scheme.Modules

end
