import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra

/-! # Elements of a monoidal object and generating families

Support for the identification of the symmetric algebra of a free sheaf with a weighted polynomial
algebra.

An *element* of an object `A` of a monoidal category is a morphism `a : 𝟙_ ⟶ A`. Two elements
`a : 𝟙_ ⟶ A`, `b : 𝟙_ ⟶ B` have a tensor `elTensor a b := λ⁻¹ ≫ (a ⊗ₘ b) : 𝟙_ ⟶ A ⊗ B`; it is
compatible with tensor products of morphisms, the associator, the braiding and the unitors
(naturality of the structural isomorphisms plus coherence on `𝟙_ ⊗ 𝟙_`).

A family `g : ι → (𝟙_ ⟶ A)` of elements *generates* `A` (`Generates g`) if morphisms out of `A`
are determined by their values on the `g i`. The generators `ιFree i` generate the free sheaf
`O_X^{⊕I}` (`free_hom_ext`), the identity generates `𝟙_`, and — the point of this file — if `gA`
generates `A` and `gB` generates `B`, then the `elTensor (gA i) (gB j)` generate `A ⊗ B`
(`Generates.tensor`). The proof uses the tensor-Hom adjunction of `X.Modules`
(`tensorObjHomEquiv`), not any colimit argument, so it applies to
`F^{⊗m}` without identifying `F^{⊗m}` with a free sheaf.

Reference: Bourbaki, Algebra III §5 (tensor products of free modules); the argument is the standard
"Hom(A ⊗ B, T) = Hom(A, Hom(B, T))" reduction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace MiyaokaMori.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor of two elements `a : 𝟙_ ⟶ A`, `b : 𝟙_ ⟶ B`: `λ⁻¹ ≫ (a ⊗ₘ b) : 𝟙_ ⟶ A ⊗ B`. -/
def elTensor {A B : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) : 𝟙_ C ⟶ A ⊗ B :=
  (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b)

@[reassoc]
theorem elTensor_comp_tensorHom {A A' B B' : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) (f : A ⟶ A')
    (g : B ⟶ B') : elTensor a b ≫ (f ⊗ₘ g) = elTensor (a ≫ f) (b ≫ g) := by
  unfold elTensor
  rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]

@[reassoc]
theorem elTensor_comp_whiskerRight {A A' B : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) (f : A ⟶ A') :
    elTensor a b ≫ (f ▷ B) = elTensor (a ≫ f) b := by
  rw [← MonoidalCategory.tensorHom_id, elTensor_comp_tensorHom, Category.comp_id]

@[reassoc]
theorem elTensor_comp_whiskerLeft {A B B' : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) (g : B ⟶ B') :
    elTensor a b ≫ (A ◁ g) = elTensor a (b ≫ g) := by
  rw [← MonoidalCategory.id_tensorHom, elTensor_comp_tensorHom, Category.comp_id]

/-- `b ≫ λ⁻¹ ≫ (a ▷ B) = elTensor a b`. -/
@[reassoc]
theorem comp_leftUnitor_inv_whiskerRight {A B : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) :
    b ≫ (λ_ B).inv ≫ (a ▷ B) = elTensor a b := by
  unfold elTensor
  rw [MonoidalCategory.tensorHom_def', ← Category.assoc, MonoidalCategory.leftUnitor_inv_naturality,
    Category.assoc]

@[reassoc]
theorem elTensor_comp_associator_hom {A B D : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) (d : 𝟙_ C ⟶ D) :
    elTensor (elTensor a b) d ≫ (α_ A B D).hom = elTensor a (elTensor b d) := by
  unfold elTensor
  have h1 : ((λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b)) ⊗ₘ d =
      ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫ ((a ⊗ₘ b) ⊗ₘ d) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have h2 : a ⊗ₘ ((λ_ (𝟙_ C)).inv ≫ (b ⊗ₘ d)) =
      (𝟙 (𝟙_ C) ⊗ₘ (λ_ (𝟙_ C)).inv) ≫ (a ⊗ₘ (b ⊗ₘ d)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have h3 : (λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom =
      (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ (λ_ (𝟙_ C)).inv) := by
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    monoidal
  rw [h1, h2, Category.assoc, Category.assoc, MonoidalCategory.associator_naturality]
  slice_lhs 1 3 => rw [h3]
  simp only [Category.assoc]

@[reassoc]
theorem elTensor_comp_associator_inv {A B D : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) (d : 𝟙_ C ⟶ D) :
    elTensor a (elTensor b d) ≫ (α_ A B D).inv = elTensor (elTensor a b) d := by
  rw [← elTensor_comp_associator_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
theorem elTensor_comp_braiding [BraidedCategory C] {A B : C} (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ B) :
    elTensor a b ≫ (β_ A B).hom = elTensor b a := by
  unfold elTensor
  rw [Category.assoc, BraidedCategory.braiding_naturality, braiding_tensorUnit_left,
    ← MonoidalCategory.unitors_inv_equal, Category.assoc, Iso.inv_hom_id_assoc]

@[reassoc]
theorem elTensor_id_comp_leftUnitor {B : C} (b : 𝟙_ C ⟶ B) :
    elTensor (𝟙 (𝟙_ C)) b ≫ (λ_ B).hom = b := by
  unfold elTensor
  rw [MonoidalCategory.id_tensorHom, Category.assoc, MonoidalCategory.leftUnitor_naturality,
    Iso.inv_hom_id_assoc]

@[reassoc]
theorem elTensor_comp_rightUnitor {A : C} (a : 𝟙_ C ⟶ A) :
    elTensor a (𝟙 (𝟙_ C)) ≫ (ρ_ A).hom = a := by
  unfold elTensor
  rw [MonoidalCategory.tensorHom_id, Category.assoc, MonoidalCategory.rightUnitor_naturality,
    MonoidalCategory.unitors_inv_equal, Iso.inv_hom_id_assoc]

theorem elTensor_id_left {B : C} (b : 𝟙_ C ⟶ B) : elTensor (𝟙 (𝟙_ C)) b = b ≫ (λ_ B).inv := by
  rw [Iso.eq_comp_inv]
  exact elTensor_id_comp_leftUnitor b

theorem elTensor_id_right {A : C} (a : 𝟙_ C ⟶ A) : elTensor a (𝟙 (𝟙_ C)) = a ≫ (ρ_ A).inv := by
  rw [Iso.eq_comp_inv]
  exact elTensor_comp_rightUnitor a

end MiyaokaMori.Monoidal

namespace AlgebraicGeometry.Scheme.Modules

open MiyaokaMori.Monoidal

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A family of elements `g i : 𝟙_ ⟶ A` generates `A`: morphisms out of `A` are determined by
their values on the `g i`. -/
def Generates {A : X.Modules} {ι : Type w} (g : ι → (𝟙_ X.Modules ⟶ A)) : Prop :=
  ∀ {T : X.Modules} (f f' : A ⟶ T), (∀ i, g i ≫ f = g i ≫ f') → f = f'

theorem Generates.of_surj {A : X.Modules} {ι : Type w} {κ : Type v}
    {g : ι → (𝟙_ X.Modules ⟶ A)} {g' : κ → (𝟙_ X.Modules ⟶ A)} (hg : Generates g)
    (h : ∀ i, ∃ j, g i = g' j) : Generates g' := by
  intro T f f' hf
  refine hg f f' fun i => ?_
  obtain ⟨j, hj⟩ := h i
  rw [hj]
  exact hf j

/-- The generators `ιFree i` generate the free sheaf `O_X^{⊕I}`. -/
theorem generates_free (I : Type u) :
    Generates (fun i : I => weightedPolynomialQCAlgebra.ιM X i) :=
  fun _ _ h => weightedPolynomialQCAlgebra.free_hom_ext X h

/-- The identity generates `𝟙_ = O_X`. -/
theorem generates_unit : Generates (fun _ : Unit => 𝟙 (𝟙_ X.Modules)) := by
  intro T f f' h
  simpa using h ()

/-- If `gA` generates `A` and `gB` generates `B`, the tensors `elTensor (gA i) (gB j)` generate
`A ⊗ B` (tensor-Hom adjunction in the first variable, then `λ_ B` to reduce to `B`). -/
theorem Generates.tensor {A B : X.Modules} {ι : Type w} {κ : Type v}
    {gA : ι → (𝟙_ X.Modules ⟶ A)} {gB : κ → (𝟙_ X.Modules ⟶ B)}
    (hA : Generates gA) (hB : Generates gB) :
    Generates (fun p : ι × κ => elTensor (gA p.1) (gB p.2)) := by
  intro T f f' h
  apply (tensorObjHomEquiv A B T).injective
  apply hA
  intro i
  rw [tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left]
  congr 1
  rw [← cancel_epi (λ_ B).inv]
  apply hB
  intro j
  rw [comp_leftUnitor_inv_whiskerRight_assoc, comp_leftUnitor_inv_whiskerRight_assoc]
  exact h (i, j)

/-- The multiplication of the weighted polynomial algebra on tensors of generators. -/
theorem elTensor_ιM_ιM_mulHom {σ : Type u} (w : σ → ℕ) (i j : ℕ) (e : weightedMonomials w i)
    (e' : weightedMonomials w j) :
    elTensor (weightedPolynomialQCAlgebra.ιM X e) (weightedPolynomialQCAlgebra.ιM X e') ≫
        weightedPolynomialQCAlgebra.mulHom X w i j =
      weightedPolynomialQCAlgebra.ιM X
        (⟨e.1 + e'.1, by simp [map_add, e.2, e'.2]⟩ : weightedMonomials w (i + j)) := by
  unfold elTensor
  rw [Category.assoc, weightedPolynomialQCAlgebra.ιM_tensor_ιM_mulHom, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules

end
