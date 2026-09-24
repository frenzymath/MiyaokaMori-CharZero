import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The two spellings of the tensor product agree

The canonical isomorphism between the two spellings of the tensor product of sheaves of modules:
`Modules.tensor A B` (the sheafification `L(G A ⊗ G B)` of the sectionwise tensor presheaf
`A.val ⊗ B.val`) and the `A ⊗ B` of the (localized) monoidal structure on `X.Modules`. Also the
section pairing `Γ(A,U) × Γ(B,U) → Γ(A ⊗ B,U)`, `a ⊗ₜ b ↦` the image under the sheafification unit.

Source: Stacks 01CA (the tensor product of sheaves of modules is the sheafification of the tensor
presheaf); Mathlib `CategoryTheory/Localization/Monoidal/Basic.lean` (`Localization.Monoidal.μ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Notation: `L` = sheafification `PresheafOfModules → X.Modules`, `G` = forget to presheaves and
   restrict scalars along `𝟙`, `L ⊣ G` (Mathlib's `sheafificationAdjunction`; `G` is fully faithful,
   so the counit `L(G A) ⟶ A` is an isomorphism, a Mathlib instance). `A ⊗ B` is the localized monoidal
   structure (`Localization.Monoidal.μ : L P ⊗ L Q ≅ L(P ⊗ Q)`); the two comparison morphisms below
   connect it with the sheafified presheaf tensor `L(G A ⊗ G B)`, both assembled from genuine
   isomorphisms. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo {X : AlgebraicGeometry.Scheme.{u}}
    (A B : X.Modules) :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorObj
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)) ⟶
      CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  (CategoryTheory.Localization.Monoidal.μ
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)).inv ≫
    CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app A)
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app B)

/- The other direction: the tensor of the inverses of the two counit isomorphisms followed by `μ`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorToSheafify {X : AlgebraicGeometry.Scheme.{u}}
    (A B : X.Modules) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B ⟶
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorObj
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)) :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
      ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app A)
      ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app B) ≫
    (CategoryTheory.Localization.Monoidal.μ
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)).hom

/- Mutual inverses: `sheafifyTensorTo = μ⁻¹ ≫ (ε_A ⊗ ε_B)`, `tensorToSheafify = (ε_A⁻¹ ⊗ ε_B⁻¹) ≫ μ`,
   directly from `tensorHom_comp_tensorHom` and `ε ≫ ε⁻¹ = 𝟙`. -/

section LocalizedAux

open MonoidalCategory Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] (L : C ⥤ D)
  (W : MorphismProperty C) [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

private theorem localized_hom_inv {P Q : C} {A B : LocalizedMonoidal L W ε}
    (eA : (toMonoidalCategory L W ε).obj P ≅ A) (eB : (toMonoidalCategory L W ε).obj Q ≅ B) :
    ((μ L W ε P Q).inv ≫ (eA.hom ⊗ₘ eB.hom)) ≫ ((eA.inv ⊗ₘ eB.inv) ≫ (μ L W ε P Q).hom) = 𝟙 _ := by
  simp [tensorHom_comp_tensorHom_assoc]

private theorem localized_inv_hom {P Q : C} {A B : LocalizedMonoidal L W ε}
    (eA : (toMonoidalCategory L W ε).obj P ≅ A) (eB : (toMonoidalCategory L W ε).obj Q ≅ B) :
    ((eA.inv ⊗ₘ eB.inv) ≫ (μ L W ε P Q).hom) ≫ ((μ L W ε P Q).inv ≫ (eA.hom ⊗ₘ eB.hom)) = 𝟙 _ := by
  simp [tensorHom_comp_tensorHom]

/-- Naturality of `μ⁻¹ ≫ (e_A ⊗ e_B)` with respect to `tensorHom` (`e` a natural family of comparison
morphisms). -/
private theorem localized_natural {P Q P' Q' : C} {A B A' B' : LocalizedMonoidal L W ε}
    (eA : (toMonoidalCategory L W ε).obj P ⟶ A) (eB : (toMonoidalCategory L W ε).obj Q ⟶ B)
    (eA' : (toMonoidalCategory L W ε).obj P' ⟶ A') (eB' : (toMonoidalCategory L W ε).obj Q' ⟶ B')
    (p : P ⟶ P') (q : Q ⟶ Q') (a : A ⟶ A') (b : B ⟶ B')
    (ha : eA ≫ a = (toMonoidalCategory L W ε).map p ≫ eA')
    (hb : eB ≫ b = (toMonoidalCategory L W ε).map q ≫ eB') :
    ((μ L W ε P Q).inv ≫ (eA ⊗ₘ eB)) ≫ (a ⊗ₘ b) =
      (toMonoidalCategory L W ε).map (p ⊗ₘ q) ≫ ((μ L W ε P' Q').inv ≫ (eA' ⊗ₘ eB')) := by
  have h := Functor.OplaxMonoidal.δ_natural (toMonoidalCategory L W ε) p q
  have hδ : ∀ X Y : C, Functor.OplaxMonoidal.δ (toMonoidalCategory L W ε) X Y = (μ L W ε X Y).inv :=
    fun _ _ => rfl
  rw [hδ, hδ] at h
  rw [Category.assoc, tensorHom_comp_tensorHom, ha, hb, ← tensorHom_comp_tensorHom,
    ← Category.assoc, ← Category.assoc, h]

end LocalizedAux

theorem AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo_comp_tensorToSheafify
    {X : AlgebraicGeometry.Scheme.{u}} (A B : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B ≫
      AlgebraicGeometry.Scheme.Modules.tensorToSheafify A B = 𝟙 _ :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  localized_hom_inv _ _ (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
    ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app A)
    ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app B)

theorem AlgebraicGeometry.Scheme.Modules.tensorToSheafify_comp_sheafifyTensorTo
    {X : AlgebraicGeometry.Scheme.{u}} (A B : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensorToSheafify A B ≫
      AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B = 𝟙 _ :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  localized_inv_hom _ _ (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
    ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app A)
    ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app B)

/-- Naturality of `sheafifyTensorTo` with respect to `tensorHom`:
`sTT_{A,B} ≫ (a ⊗ b) = L(G a ⊗ G b) ≫ sTT_{A',B'}` (naturality of `μ` and of the sheafification
counit). -/
theorem AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo_naturality
    {X : AlgebraicGeometry.Scheme.{u}} {A B A' B' : X.Modules} (a : A ⟶ A') (b : B ⟶ B') :
    AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) a b =
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (CategoryTheory.MonoidalCategoryStruct.tensorHom
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map a)
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map b)) ≫
      AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A' B' :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  localized_natural _ _ (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X) _ _ _ _ _ _ a b
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality a).symm
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality b).symm

/- The canonical isomorphism between `Modules.tensor A B` (the sheafification `L(G A ⊗ G B)` of the
   sectionwise tensor presheaf) and the monoidal `A ⊗ B`: `hom = sheafifyTensorTo`,
   `inv = tensorToSheafify`, both assembled from `μ` and the sheafification counit. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj {X : AlgebraicGeometry.Scheme.{u}}
    (A B : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor A B ≅ CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B where
  hom := AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B
  inv := AlgebraicGeometry.Scheme.Modules.tensorToSheafify A B
  hom_inv_id := AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo_comp_tensorToSheafify A B
  inv_hom_id := AlgebraicGeometry.Scheme.Modules.tensorToSheafify_comp_sheafifyTensorTo A B

/-- The section pairing `Γ(A, U) × Γ(B, U) → Γ(A ⊗ B, U)`: `a ⊗ₜ b ∈ (G A ⊗ G B)(U)` (the presheaf
tensor product is the module tensor product openwise), sent by the sheafification unit into
`L(G A ⊗ G B)(U)` and then by `sheafifyTensorTo` into `(A ⊗ B)(U)`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorSections {X : AlgebraicGeometry.Scheme.{u}}
    (A B : X.Modules) (U : X.Opens) (a : A.val.obj (Opposite.op U)) (b : B.val.obj (Opposite.op U)) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).val.obj (Opposite.op U) :=
  (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app (Opposite.op U)
    (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B))).app
      (Opposite.op U) (TensorProduct.tmul _ a b))

/-- `tensorToSheafify` applied to a section pairing gives back the image under the sheafification
unit. -/
theorem AlgebraicGeometry.Scheme.Modules.tensorToSheafify_tensorSections {X : AlgebraicGeometry.Scheme.{u}}
    (A B : X.Modules) (U : X.Opens) (a : A.val.obj (Opposite.op U)) (b : B.val.obj (Opposite.op U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorToSheafify A B).val.app (Opposite.op U)
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (CategoryTheory.MonoidalCategoryStruct.tensorObj
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B))).app
        (Opposite.op U) (TensorProduct.tmul _ a b) := by
  have h := AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo_comp_tensorToSheafify A B
  exact congrArg (fun k => k.val.app (Opposite.op U)
    (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B))).app
      (Opposite.op U) (TensorProduct.tmul _ a b))) h

/-- The section pairing is natural with respect to `tensorHom`: `(φ ⊗ ψ)(a ⊗ b) = φ a ⊗ ψ b`. -/
theorem AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections {X : AlgebraicGeometry.Scheme.{u}}
    {A B A' B' : X.Modules} (φ : A ⟶ A') (ψ : B ⟶ B') (U : X.Opens)
    (a : A.val.obj (Opposite.op U)) (b : B.val.obj (Opposite.op U)) :
    (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) φ ψ).val.app (Opposite.op U)
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B' U
        (φ.val.app (Opposite.op U) a) (ψ.val.app (Opposite.op U) b) := by
  have h := AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo_naturality φ ψ
  have hη := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (CategoryTheory.MonoidalCategoryStruct.tensorHom
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map ψ))
  have h1 := congrArg (fun k => k.val.app (Opposite.op U)
    (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B))).app
      (Opposite.op U) (TensorProduct.tmul _ a b))) h
  have h2 := congrArg (fun k => k.app (Opposite.op U) (TensorProduct.tmul _ a b)) hη
  refine h1.trans ?_
  exact congrArg ((AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A' B').val.app (Opposite.op U)) h2.symm

end
