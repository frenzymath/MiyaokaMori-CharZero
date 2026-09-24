import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-! # Coherence of the section pairing with the symmetric monoidal structure

Compatibility of the section pairing `Modules.tensorSections` of the tensor product with the symmetric
monoidal structure on `X.Modules`: the values of the left/right unitors, the braiding and the
associator on pure tensor sections.

Method: first prove four morphism identities at the abstract level of "the comparison
`δ F P Q ≫ (eA ⊗ₘ eB)` of a monoidal functor `F`" (Mathlib's `Functor.OplaxMonoidal`:
`δ_comp_η_tensorHom` / `δ_comp_tensorHom_η` / `associativity` and `Functor.map_braiding`), then
specialize to `L' = Localization.Monoidal.toMonoidalCategory` (where
`δ L' P Q = (Localization.Monoidal.μ …).inv` and `η L' = ε.hom`), and finally evaluate pointwise via
the naturality of the unit of the sheafification adjunction and the triangle identity.

Source: Stacks 01CA; Mathlib `CategoryTheory/Localization/Monoidal/Basic.lean`, `Monoidal/Functor.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Category MonoidalCategory Opposite
open CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.LaxMonoidal
open scoped AlgebraicGeometry

noncomputable section

/-- The symmetric monoidal structure on presheaves of modules, transported to `X.ringCatSheaf.obj`
(compatible with `AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory`). -/
noncomputable instance AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
    (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.SymmetricCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (CategoryTheory.SymmetricCategory
    (_root_.PresheafOfModules.{u} (X.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat)))

namespace AlgebraicGeometry.Scheme.Modules.MonoidalAux

section Monoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

theorem delta_tensorHom_leftUnitor {Q : C} {B : D} (eB : F.obj Q ⟶ B) :
    (δ F (𝟙_ C) Q ≫ (η F ⊗ₘ eB)) ≫ (λ_ B).hom = F.map (λ_ Q).hom ≫ eB := by
  rw [δ_comp_η_tensorHom, assoc, assoc, MonoidalCategory.leftUnitor_naturality, Iso.inv_hom_id_assoc]

theorem delta_tensorHom_rightUnitor {P : C} {A : D} (eA : F.obj P ⟶ A) :
    (δ F P (𝟙_ C) ≫ (eA ⊗ₘ η F)) ≫ (ρ_ A).hom = F.map (ρ_ P).hom ≫ eA := by
  rw [δ_comp_tensorHom_η, assoc, assoc, MonoidalCategory.rightUnitor_naturality, Iso.inv_hom_id_assoc]

theorem delta_tensorHom_associator {P Q R : C} {A B E : D}
    (eA : F.obj P ⟶ A) (eB : F.obj Q ⟶ B) (eC : F.obj R ⟶ E) :
    (δ F (P ⊗ Q) R ≫ ((δ F P Q ≫ (eA ⊗ₘ eB)) ⊗ₘ eC)) ≫ (α_ A B E).hom =
      F.map (α_ P Q R).hom ≫ (δ F P (Q ⊗ R) ≫ (eA ⊗ₘ (δ F Q R ≫ (eB ⊗ₘ eC)))) := by
  have h1 : (δ F P Q ≫ (eA ⊗ₘ eB)) ⊗ₘ eC
      = (δ F P Q ▷ F.obj R) ≫ ((eA ⊗ₘ eB) ⊗ₘ eC) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, id_comp]
  have h2 : eA ⊗ₘ (δ F Q R ≫ (eB ⊗ₘ eC))
      = (F.obj P ◁ δ F Q R) ≫ (eA ⊗ₘ (eB ⊗ₘ eC)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, id_comp]
  rw [h1, h2, assoc, assoc, MonoidalCategory.associator_naturality,
    Functor.OplaxMonoidal.associativity_assoc]

theorem delta_whiskerRight_comp {P P' R : C} {A E : D} (f : P ⟶ P')
    (eA : F.obj P' ⟶ A) (eC : F.obj R ⟶ E) :
    F.map (f ▷ R) ≫ (δ F P' R ≫ (eA ⊗ₘ eC)) = δ F P R ≫ ((F.map f ≫ eA) ⊗ₘ eC) := by
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, ← tensorHom_id,
    tensorHom_comp_tensorHom, id_comp]

theorem delta_whiskerLeft_comp {P Q Q' : C} {A B : D} (g : Q ⟶ Q')
    (eA : F.obj P ⟶ A) (eB : F.obj Q' ⟶ B) :
    F.map (P ◁ g) ≫ (δ F P Q' ≫ (eA ⊗ₘ eB)) = δ F P Q ≫ (eA ⊗ₘ (F.map g ≫ eB)) := by
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc, ← id_tensorHom,
    tensorHom_comp_tensorHom, id_comp]

/-- The "transposed" form of associativity: the pairwise comparison morphisms written as `F.map s ≫ e`. -/
theorem delta_tensorHom_associator' {P Q R PQ QR : C} {A B E : D}
    (eA : F.obj P ⟶ A) (eB : F.obj Q ⟶ B) (eC : F.obj R ⟶ E)
    (sAB : P ⊗ Q ⟶ PQ) (sBC : Q ⊗ R ⟶ QR)
    (eAB : F.obj PQ ⟶ A ⊗ B) (eBC : F.obj QR ⟶ B ⊗ E)
    (hAB : F.map sAB ≫ eAB = δ F P Q ≫ (eA ⊗ₘ eB))
    (hBC : F.map sBC ≫ eBC = δ F Q R ≫ (eB ⊗ₘ eC)) :
    (F.map (sAB ▷ R) ≫ (δ F PQ R ≫ (eAB ⊗ₘ eC))) ≫ (α_ A B E).hom =
      F.map (α_ P Q R).hom ≫ (F.map (P ◁ sBC) ≫ (δ F P QR ≫ (eA ⊗ₘ eBC))) := by
  rw [delta_whiskerRight_comp, hAB, delta_whiskerLeft_comp, hBC,
    delta_tensorHom_associator]

end Monoidal

section Braided

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided]

theorem delta_tensorHom_braiding {P Q : C} {A B : D} (eA : F.obj P ⟶ A) (eB : F.obj Q ⟶ B) :
    (δ F P Q ≫ (eA ⊗ₘ eB)) ≫ (β_ A B).hom =
      F.map (β_ P Q).hom ≫ (δ F Q P ≫ (eB ⊗ₘ eA)) := by
  rw [assoc, BraidedCategory.braiding_naturality, Functor.map_braiding, assoc, assoc,
    Functor.Monoidal.μ_δ_assoc]

end Braided

end AlgebraicGeometry.Scheme.Modules.MonoidalAux

namespace AlgebraicGeometry.Scheme.Modules.MonoidalAux

section Loc

open CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] (L : C ⥤ D)
  (W : MorphismProperty C) [W.IsMonoidal] [L.IsLocalization W] {unit : D}
  (ε : L.obj (𝟙_ C) ≅ unit)

theorem loc_leftUnitor {Q : C} {B : LocalizedMonoidal L W ε}
    (eB : (toMonoidalCategory L W ε).obj Q ⟶ B) :
    ((μ L W ε (𝟙_ C) Q).inv ≫ ((ε' L W ε).hom ⊗ₘ eB)) ≫ (λ_ B).hom =
      (toMonoidalCategory L W ε).map (λ_ Q).hom ≫ eB :=
  delta_tensorHom_leftUnitor (toMonoidalCategory L W ε) eB

theorem loc_rightUnitor {P : C} {A : LocalizedMonoidal L W ε}
    (eA : (toMonoidalCategory L W ε).obj P ⟶ A) :
    ((μ L W ε P (𝟙_ C)).inv ≫ (eA ⊗ₘ (ε' L W ε).hom)) ≫ (ρ_ A).hom =
      (toMonoidalCategory L W ε).map (ρ_ P).hom ≫ eA :=
  delta_tensorHom_rightUnitor (toMonoidalCategory L W ε) eA

theorem loc_associator {P Q R : C} {A B E : LocalizedMonoidal L W ε}
    (eA : (toMonoidalCategory L W ε).obj P ⟶ A) (eB : (toMonoidalCategory L W ε).obj Q ⟶ B)
    (eC : (toMonoidalCategory L W ε).obj R ⟶ E) :
    ((μ L W ε (P ⊗ Q) R).inv ≫ (((μ L W ε P Q).inv ≫ (eA ⊗ₘ eB)) ⊗ₘ eC)) ≫ (α_ A B E).hom =
      (toMonoidalCategory L W ε).map (α_ P Q R).hom ≫
        ((μ L W ε P (Q ⊗ R)).inv ≫ (eA ⊗ₘ ((μ L W ε Q R).inv ≫ (eB ⊗ₘ eC)))) :=
  delta_tensorHom_associator (toMonoidalCategory L W ε) eA eB eC

theorem loc_whiskerRight_comp {P P' R : C} {A E : LocalizedMonoidal L W ε} (f : P ⟶ P')
    (eA : (toMonoidalCategory L W ε).obj P' ⟶ A) (eC : (toMonoidalCategory L W ε).obj R ⟶ E) :
    (toMonoidalCategory L W ε).map (f ▷ R) ≫ ((μ L W ε P' R).inv ≫ (eA ⊗ₘ eC)) =
      (μ L W ε P R).inv ≫ (((toMonoidalCategory L W ε).map f ≫ eA) ⊗ₘ eC) :=
  delta_whiskerRight_comp (toMonoidalCategory L W ε) f eA eC

theorem loc_associator' {P Q R PQ QR : C} {A B E : LocalizedMonoidal L W ε}
    (eA : (toMonoidalCategory L W ε).obj P ⟶ A) (eB : (toMonoidalCategory L W ε).obj Q ⟶ B)
    (eC : (toMonoidalCategory L W ε).obj R ⟶ E)
    (sAB : P ⊗ Q ⟶ PQ) (sBC : Q ⊗ R ⟶ QR)
    (eAB : (toMonoidalCategory L W ε).obj PQ ⟶ A ⊗ B)
    (eBC : (toMonoidalCategory L W ε).obj QR ⟶ B ⊗ E)
    (hAB : (toMonoidalCategory L W ε).map sAB ≫ eAB = (μ L W ε P Q).inv ≫ (eA ⊗ₘ eB))
    (hBC : (toMonoidalCategory L W ε).map sBC ≫ eBC = (μ L W ε Q R).inv ≫ (eB ⊗ₘ eC)) :
    ((toMonoidalCategory L W ε).map (sAB ▷ R) ≫ ((μ L W ε PQ R).inv ≫ (eAB ⊗ₘ eC))) ≫
        (α_ A B E).hom =
      (toMonoidalCategory L W ε).map (α_ P Q R).hom ≫
        ((toMonoidalCategory L W ε).map (P ◁ sBC) ≫ ((μ L W ε P QR).inv ≫ (eA ⊗ₘ eBC))) :=
  delta_tensorHom_associator' (toMonoidalCategory L W ε) eA eB eC sAB sBC eAB eBC hAB hBC

theorem loc_braiding [BraidedCategory C] {P Q : C} {A B : LocalizedMonoidal L W ε}
    (eA : (toMonoidalCategory L W ε).obj P ⟶ A) (eB : (toMonoidalCategory L W ε).obj Q ⟶ B) :
    ((μ L W ε P Q).inv ≫ (eA ⊗ₘ eB)) ≫ (β_ A B).hom =
      (toMonoidalCategory L W ε).map (β_ P Q).hom ≫ ((μ L W ε Q P).inv ≫ (eB ⊗ₘ eA)) :=
  delta_tensorHom_braiding (toMonoidalCategory L W ε) eA eB

end Loc

end AlgebraicGeometry.Scheme.Modules.MonoidalAux

namespace AlgebraicGeometry.Scheme.Modules

/-- The sheafification functor `L`. -/
abbrev shL (X : AlgebraicGeometry.Scheme.{u}) :=
  _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The right adjoint `G`. -/
abbrev shG (X : AlgebraicGeometry.Scheme.{u}) :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)

/-- The sheafification adjunction `L ⊣ G`. -/
abbrev shAdj (X : AlgebraicGeometry.Scheme.{u}) :=
  _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

/-- Sheafification inverts `W`. -/
abbrev shW (X : AlgebraicGeometry.Scheme.{u}) :=
  (CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))

instance shW_isMonoidal (X : AlgebraicGeometry.Scheme.{u}) : (shW X).IsMonoidal :=
  AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X

instance shL_isLocalization (X : AlgebraicGeometry.Scheme.{u}) :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization (shW X) :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- (P) `L f ≫ g` applied to the image of the sheafification unit: naturality of the unit. -/
theorem sheafify_unit_eval {P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj}
    {A : X.Modules} (f : P ⟶ Q) (g : (shL X).obj Q ⟶ A) (U : X.Opens) (p : P.obj (op U)) :
    ((shL X).map f ≫ g).val.app (op U) (((shAdj X).unit.app P).app (op U) p) =
      g.val.app (op U) (((shAdj X).unit.app Q).app (op U) (f.app (op U) p)) := by
  have hη := (shAdj X).unit.naturality f
  have h2 := congrArg (fun k => k.app (op U) p) hη
  exact congrArg (g.val.app (op U)) h2.symm

/-- (E) The pointwise form of the triangle identity of the adjunction. -/
theorem sheafify_unit_counit_eval {P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj}
    {A : X.Modules} (f : P ⟶ (shG X).obj A) (U : X.Opens) (p : P.obj (op U)) :
    ((shL X).map f ≫ (shAdj X).counit.app A).val.app (op U)
        (((shAdj X).unit.app P).app (op U) p) = f.app (op U) p := by
  rw [sheafify_unit_eval]
  have ht := (shAdj X).right_triangle_components (Y := A)
  exact congrArg (fun k => k.app (op U) (f.app (op U) p)) ht

/-- The presheaf-level morphism `σ_{A,B} : G A ⊗ G B ⟶ G (A ⊗ B)` of the section pairing (the transpose
of `sheafifyTensorTo` under the sheafification adjunction). -/
def tensorSectionsHom (A B : X.Modules) :
    (shG X).obj A ⊗ (shG X).obj B ⟶ (shG X).obj
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) :=
  (shAdj X).homEquiv _ _ (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B)

theorem tensorSectionsHom_app (A B : X.Modules) (U : X.Opens)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (tensorSectionsHom A B).app (op U)
        (TensorProduct.tmul _ a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b :=
  rfl

theorem sheafify_tensorSectionsHom (A B : X.Modules) :
    (shL X).map (tensorSectionsHom A B) ≫ (shAdj X).counit.app
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) =
      AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B :=
  (shAdj X).homEquiv_symm_apply _ _ _ ▸
    ((shAdj X).homEquiv _ _).symm_apply_apply
      (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B)

theorem sheafifyTensorTo_comp_leftUnitor (A : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo (𝟙_ X.Modules) A ≫ (λ_ A).hom =
      (shL X).map (λ_ ((shG X).obj A)).hom ≫ (shAdj X).counit.app A :=
  AlgebraicGeometry.Scheme.Modules.MonoidalAux.loc_leftUnitor _ _ (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
    ((shAdj X).counit.app A)


/-- **(L) The left unitor on section pairings**: `(λ_ A).hom` sends `r ⊗ a` to `r • a`. -/
theorem leftUnitor_app_tensorSections (A : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (a : Γ(A, U)) :
    (λ_ A).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) A U r a) = r • a := by
  have h1 : (λ_ A).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) A U r a) =
      (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo (𝟙_ X.Modules) A ≫
        (λ_ A).hom).val.app (op U)
          (((shAdj X).unit.app
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              ((shG X).obj (𝟙_ X.Modules)) ((shG X).obj A))).app (op U)
            (TensorProduct.tmul _ r a)) := rfl
  rw [h1, sheafifyTensorTo_comp_leftUnitor]
  refine (sheafify_unit_counit_eval (X := X) (A := A) (λ_ ((shG X).obj A)).hom U
    (TensorProduct.tmul _ r a)).trans ?_
  exact TensorProduct.lid_tmul a r

theorem sheafifyTensorTo_comp_rightUnitor (A : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A (𝟙_ X.Modules) ≫ (ρ_ A).hom =
      (shL X).map (ρ_ ((shG X).obj A)).hom ≫ (shAdj X).counit.app A :=
  AlgebraicGeometry.Scheme.Modules.MonoidalAux.loc_rightUnitor _ _
    (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X) ((shAdj X).counit.app A)

theorem sheafifyTensorTo_comp_braiding (A B : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B ≫ (β_ A B).hom =
      (shL X).map (β_ ((shG X).obj A) ((shG X).obj B)).hom ≫
        AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo B A :=
  AlgebraicGeometry.Scheme.Modules.MonoidalAux.loc_braiding _ _
    (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
    ((shAdj X).counit.app A) ((shAdj X).counit.app B)

theorem sheafifyTensorTo_comp_associator (A B C : X.Modules) :
    ((shL X).map (tensorSectionsHom A B ▷ (shG X).obj C) ≫
        AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) C) ≫
        (α_ A B C).hom =
      (shL X).map (α_ ((shG X).obj A) ((shG X).obj B) ((shG X).obj C)).hom ≫
        ((shL X).map ((shG X).obj A ◁ tensorSectionsHom B C) ≫
          AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A
            (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C)) :=
  AlgebraicGeometry.Scheme.Modules.MonoidalAux.loc_associator' _ _
    (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
    ((shAdj X).counit.app A) ((shAdj X).counit.app B) ((shAdj X).counit.app C)
    (tensorSectionsHom A B) (tensorSectionsHom B C)
    ((shAdj X).counit.app _) ((shAdj X).counit.app _)
    (sheafify_tensorSectionsHom A B) (sheafify_tensorSectionsHom B C)

/-- **(R) The right unitor on section pairings.** -/
theorem rightUnitor_app_tensorSections (A : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (r : Γ(X, U)) :
    (ρ_ A).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A (𝟙_ X.Modules) U a r) = r • a := by
  have h1 : (ρ_ A).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A (𝟙_ X.Modules) U a r) =
      (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A (𝟙_ X.Modules) ≫
        (ρ_ A).hom).val.app (op U)
          (((shAdj X).unit.app
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              ((shG X).obj A) ((shG X).obj (𝟙_ X.Modules)))).app (op U)
            (TensorProduct.tmul _ a r)) := rfl
  rw [h1, sheafifyTensorTo_comp_rightUnitor]
  refine (sheafify_unit_counit_eval (X := X) (A := A) (ρ_ ((shG X).obj A)).hom U
    (TensorProduct.tmul _ a r)).trans ?_
  exact TensorProduct.rid_tmul a r

/-- **(β) The braiding on section pairings.** -/
theorem braiding_app_tensorSections (A B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (β_ A B).hom.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections B A U b a := by
  have h1 : (β_ A B).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B ≫ (β_ A B).hom).val.app (op U)
          (((shAdj X).unit.app
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              ((shG X).obj A) ((shG X).obj B))).app (op U)
            (TensorProduct.tmul _ a b)) := rfl
  rw [h1, sheafifyTensorTo_comp_braiding]
  exact sheafify_unit_eval (X := X) (β_ ((shG X).obj A) ((shG X).obj B)).hom
    (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo B A) U (TensorProduct.tmul _ a b)

/-- **(α) The associator on section pairings.** -/
theorem associator_app_tensorSections (A B C : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    (α_ A B C).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) C U
          (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) c) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C) U a
        (AlgebraicGeometry.Scheme.Modules.tensorSections B C U b c) := by
  have h1 : (α_ A B C).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) C U
          (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) c) =
      (((shL X).map (tensorSectionsHom A B ▷ (shG X).obj C) ≫
          AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
            (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) C) ≫
        (α_ A B C).hom).val.app (op U)
          (((shAdj X).unit.app
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              (CategoryTheory.MonoidalCategoryStruct.tensorObj
                ((shG X).obj A) ((shG X).obj B)) ((shG X).obj C))).app (op U)
            (TensorProduct.tmul _ (TensorProduct.tmul _ a b) c)) := by
    refine congrArg ((α_ A B C).hom.app U) ?_
    exact (sheafify_unit_eval (X := X) (tensorSectionsHom A B ▷ (shG X).obj C)
      (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) C) U
      (TensorProduct.tmul _ (TensorProduct.tmul _ a b) c)).symm
  rw [h1, sheafifyTensorTo_comp_associator]
  refine (sheafify_unit_eval (X := X)
    (α_ ((shG X).obj A) ((shG X).obj B) ((shG X).obj C)).hom _ U
    (TensorProduct.tmul _ (TensorProduct.tmul _ a b) c)).trans ?_
  exact sheafify_unit_eval (X := X) ((shG X).obj A ◁ tensorSectionsHom B C)
    (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B C)) U
    (TensorProduct.tmul _ a (TensorProduct.tmul _ b c))

end AlgebraicGeometry.Scheme.Modules

end
