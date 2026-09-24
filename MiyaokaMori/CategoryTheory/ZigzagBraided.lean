import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Zigzag identities in a braided monoidal category

Abstract zigzag ("snake") identities in a braided monoidal category, for a pair
`c : 𝟙 ⟶ D ⊗ V` ("coevaluation") and `ev : D ⊗ V ⟶ 𝟙` ("evaluation") that both have the dual
factor `D` on the *left* (the shape of `coevSection`/`dualEv`).

* `Z1 c ev`, `Z2 c ev`: the two zigzag identities, written with the braiding.
* `lemmaB` (from `Z1`): for `ψ : D ⟶ 𝟙`, `(ρ_ D).inv ≫ D ◁ (c ≫ ψ ▷ V ≫ (λ_ V).hom) ≫ ev = ψ`
  — "the functional attached to the section `(ψ ⊗ id)(c)` is `ψ`".
* `lemmaA` (from `Z2`): for `σ : 𝟙 ⟶ V`, `c ≫ ((ρ_ D).inv ≫ D ◁ σ ≫ ev) ▷ V ≫ (λ_ V).hom = σ`
  — "the section attached to the functional `φ ↦ ⟨φ, σ⟩` is `σ`".
* `Z1_map`, `Z2_map`: transport along a braided strong monoidal functor `F`, with
  `c_F := ε ≫ F.map c ≫ δ` and `ev_F := μ ≫ F.map ev ≫ η`.

Source: Stacks 01CM/01CN (evaluation/coevaluation of a locally free module); standard rigid-category
algebra (Mathlib `CategoryTheory.Monoidal.Rigid.Basic` uses the other-sided convention, hence the braidings).
Used for the correspondence between sections of a vector bundle and linear functionals on its total
space (Definition 2.1 of the paper).
-/

set_option autoImplicit false

universe v u v' u'

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory.Zigzag

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- First zigzag identity: `φ ↦ Σ_j ⟨φ, e_j⟩ e_j^∨ = φ`. -/
def Z1 {D V : C} (c : 𝟙_ C ⟶ D ⊗ V) (ev : D ⊗ V ⟶ 𝟙_ C) : Prop :=
  (ρ_ D).inv ≫ D ◁ c ≫ (α_ D D V).inv ≫ (β_ D D).hom ▷ V ≫ (α_ D D V).hom ≫ D ◁ ev ≫
    (ρ_ D).hom = 𝟙 D

/-- Second zigzag identity: `v ↦ Σ_j ⟨e_j^∨, v⟩ e_j = v`. -/
def Z2 {D V : C} (c : 𝟙_ C ⟶ D ⊗ V) (ev : D ⊗ V ⟶ 𝟙_ C) : Prop :=
  (λ_ V).inv ≫ c ▷ V ≫ (α_ D V V).hom ≫ D ◁ (β_ V V).hom ≫ (α_ D V V).inv ≫ ev ▷ V ≫
    (λ_ V).hom = 𝟙 V

/-- `D ◁ ψ ≫ ρ = β ≫ ψ ▷ D ≫ λ` for `ψ : D ⟶ 𝟙`. -/
theorem whiskerLeft_rightUnitor_eq {D : C} (ψ : D ⟶ 𝟙_ C) :
    D ◁ ψ ≫ (ρ_ D).hom = (β_ D D).hom ≫ ψ ▷ D ≫ (λ_ D).hom := by
  have h := BraidedCategory.braiding_naturality_right D ψ
  rw [braiding_tensorUnit_right] at h
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Moving `ψ : D ⟶ 𝟙` through the evaluation. -/
theorem whiskerLeft_whiskerRight_leftUnitor_comp {D V : C} (ψ : D ⟶ 𝟙_ C) (ev : D ⊗ V ⟶ 𝟙_ C) :
    D ◁ (ψ ▷ V) ≫ D ◁ (λ_ V).hom ≫ ev =
      (α_ D D V).inv ≫ (β_ D D).hom ▷ V ≫ (α_ D D V).hom ≫ D ◁ ev ≫ (ρ_ D).hom ≫ ψ := by
  have h1 : D ◁ (ψ ▷ V) = (α_ D D V).inv ≫ (D ◁ ψ) ▷ V ≫ (α_ D (𝟙_ C) V).hom := by
    rw [associator_naturality_middle, Iso.inv_hom_id_assoc]
  have h3 : (λ_ D).hom ▷ V = (α_ (𝟙_ C) D V).hom ≫ (λ_ (D ⊗ V)).hom := by
    rw [leftUnitor_tensor_hom, Iso.hom_inv_id_assoc]
  have h4 : ψ ▷ (D ⊗ V) ≫ (λ_ (D ⊗ V)).hom ≫ ev = D ◁ ev ≫ (ρ_ D).hom ≫ ψ := by
    rw [← leftUnitor_naturality, ← Category.assoc, ← whisker_exchange, Category.assoc,
      unitors_equal, rightUnitor_naturality]
  calc D ◁ (ψ ▷ V) ≫ D ◁ (λ_ V).hom ≫ ev
      = (α_ D D V).inv ≫ (D ◁ ψ) ▷ V ≫ (α_ D (𝟙_ C) V).hom ≫ D ◁ (λ_ V).hom ≫ ev := by
        rw [h1]; simp only [Category.assoc]
    _ = (α_ D D V).inv ≫ (D ◁ ψ) ▷ V ≫ (ρ_ D).hom ▷ V ≫ ev := by
        rw [← Category.assoc (α_ D (𝟙_ C) V).hom, triangle]
    _ = (α_ D D V).inv ≫ ((β_ D D).hom ≫ ψ ▷ D ≫ (λ_ D).hom) ▷ V ≫ ev := by
        rw [← Category.assoc ((D ◁ ψ) ▷ V), ← comp_whiskerRight, whiskerLeft_rightUnitor_eq]
    _ = (α_ D D V).inv ≫ (β_ D D).hom ▷ V ≫ (ψ ▷ D) ▷ V ≫ (α_ (𝟙_ C) D V).hom ≫
          (λ_ (D ⊗ V)).hom ≫ ev := by
        rw [comp_whiskerRight, comp_whiskerRight, h3]; simp only [Category.assoc]
    _ = (α_ D D V).inv ≫ (β_ D D).hom ▷ V ≫ (α_ D D V).hom ≫ ψ ▷ (D ⊗ V) ≫
          (λ_ (D ⊗ V)).hom ≫ ev := by
        rw [← Category.assoc ((ψ ▷ D) ▷ V), associator_naturality_left]; simp only [Category.assoc]
    _ = (α_ D D V).inv ≫ (β_ D D).hom ▷ V ≫ (α_ D D V).hom ≫ D ◁ ev ≫ (ρ_ D).hom ≫ ψ := by
        rw [h4]

/-- **Lemma B**: from `Z1`, the functional attached to the section `c ≫ ψ ▷ V ≫ λ` is `ψ`. -/
theorem lemmaB {D V : C} {c : 𝟙_ C ⟶ D ⊗ V} {ev : D ⊗ V ⟶ 𝟙_ C} (h : Z1 c ev) (ψ : D ⟶ 𝟙_ C) :
    (ρ_ D).inv ≫ D ◁ (c ≫ ψ ▷ V ≫ (λ_ V).hom) ≫ ev = ψ := by
  have h' := reassoc_of% h
  calc (ρ_ D).inv ≫ D ◁ (c ≫ ψ ▷ V ≫ (λ_ V).hom) ≫ ev
      = (ρ_ D).inv ≫ D ◁ c ≫ (D ◁ (ψ ▷ V) ≫ D ◁ (λ_ V).hom ≫ ev) := by
        simp only [whiskerLeft_comp, Category.assoc]
    _ = (ρ_ D).inv ≫ D ◁ c ≫ (α_ D D V).inv ≫ (β_ D D).hom ▷ V ≫ (α_ D D V).hom ≫ D ◁ ev ≫
          (ρ_ D).hom ≫ ψ := by
        rw [whiskerLeft_whiskerRight_leftUnitor_comp]
    _ = ψ := h' ψ

/-- Moving `σ : 𝟙 ⟶ V` through the coevaluation. -/
theorem comp_leftUnitor_inv_whiskerRight {D V : C} (σ : 𝟙_ C ⟶ V) (c : 𝟙_ C ⟶ D ⊗ V) :
    σ ≫ (λ_ V).inv ≫ c ▷ V ≫ (α_ D V V).hom ≫ D ◁ (β_ V V).hom ≫ (α_ D V V).inv =
      c ≫ (ρ_ D).inv ▷ V ≫ (D ◁ σ) ▷ V := by
  have h6 : (ρ_ V).inv ≫ V ◁ σ ≫ (β_ V V).hom = (λ_ V).inv ≫ σ ▷ V := by
    rw [BraidedCategory.braiding_naturality_right, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
  calc σ ≫ (λ_ V).inv ≫ c ▷ V ≫ (α_ D V V).hom ≫ D ◁ (β_ V V).hom ≫ (α_ D V V).inv
      = (λ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ σ ≫ c ▷ V ≫ (α_ D V V).hom ≫ D ◁ (β_ V V).hom ≫
          (α_ D V V).inv := by
        rw [← Category.assoc, leftUnitor_inv_naturality]; simp only [Category.assoc]
    _ = (ρ_ (𝟙_ C)).inv ≫ c ▷ 𝟙_ C ≫ (D ⊗ V) ◁ σ ≫ (α_ D V V).hom ≫ D ◁ (β_ V V).hom ≫
          (α_ D V V).inv := by
        rw [← Category.assoc (𝟙_ C ◁ σ), whisker_exchange, unitors_inv_equal]
        simp only [Category.assoc]
    _ = c ≫ (ρ_ (D ⊗ V)).inv ≫ (D ⊗ V) ◁ σ ≫ (α_ D V V).hom ≫ D ◁ (β_ V V).hom ≫
          (α_ D V V).inv := by
        rw [← Category.assoc (ρ_ (𝟙_ C)).inv, ← rightUnitor_inv_naturality]
        simp only [Category.assoc]
    _ = c ≫ D ◁ (ρ_ V).inv ≫ ((α_ D V (𝟙_ C)).inv ≫ (D ⊗ V) ◁ σ ≫ (α_ D V V).hom) ≫
          D ◁ (β_ V V).hom ≫ (α_ D V V).inv := by
        rw [rightUnitor_tensor_inv]; simp only [Category.assoc]
    _ = c ≫ D ◁ ((ρ_ V).inv ≫ V ◁ σ ≫ (β_ V V).hom) ≫ (α_ D V V).inv := by
        rw [associator_naturality_right, Iso.inv_hom_id_assoc]
        simp only [whiskerLeft_comp, Category.assoc]
    _ = c ≫ D ◁ (λ_ V).inv ≫ D ◁ (σ ▷ V) ≫ (α_ D V V).inv := by
        rw [h6]; simp only [whiskerLeft_comp, Category.assoc]
    _ = c ≫ (D ◁ (λ_ V).inv ≫ (α_ D (𝟙_ C) V).inv) ≫ (D ◁ σ) ▷ V := by
        rw [associator_inv_naturality_middle]; simp only [Category.assoc]
    _ = c ≫ (ρ_ D).inv ▷ V ≫ (D ◁ σ) ▷ V := by
        rw [triangle_assoc_comp_left_inv]

/-- **Lemma A**: from `Z2`, the section attached to the functional `(ρ_ D).inv ≫ D ◁ σ ≫ ev` is `σ`. -/
theorem lemmaA {D V : C} {c : 𝟙_ C ⟶ D ⊗ V} {ev : D ⊗ V ⟶ 𝟙_ C} (h : Z2 c ev) (σ : 𝟙_ C ⟶ V) :
    c ≫ ((ρ_ D).inv ≫ D ◁ σ ≫ ev) ▷ V ≫ (λ_ V).hom = σ := by
  have h' := reassoc_of% h
  calc c ≫ ((ρ_ D).inv ≫ D ◁ σ ≫ ev) ▷ V ≫ (λ_ V).hom
      = (c ≫ (ρ_ D).inv ▷ V ≫ (D ◁ σ) ▷ V) ≫ ev ▷ V ≫ (λ_ V).hom := by
        simp only [comp_whiskerRight, Category.assoc]
    _ = (σ ≫ (λ_ V).inv ≫ c ▷ V ≫ (α_ D V V).hom ≫ D ◁ (β_ V V).hom ≫ (α_ D V V).inv) ≫
          ev ▷ V ≫ (λ_ V).hom := by
        rw [comp_leftUnitor_inv_whiskerRight]
    _ = σ := by
        simp only [Category.assoc]
        rw [h, Category.comp_id]

section Transport

variable {D' : Type u'} [Category.{v'} D'] [MonoidalCategory D'] [BraidedCategory D']
variable (F : C ⥤ D') [F.Braided]

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- Transport of the first zigzag identity along a braided strong monoidal functor. -/
theorem Z1_map {D V : C} {c : 𝟙_ C ⟶ D ⊗ V} {ev : D ⊗ V ⟶ 𝟙_ C} (h : Z1 c ev) :
    Z1 (ε F ≫ F.map c ≫ δ F D V) (μ F D V ≫ F.map ev ≫ η F) := by
  unfold Z1 at h ⊢
  have h' := congrArg F.map h
  simp only [Functor.map_comp, Functor.map_id, Functor.Monoidal.map_rightUnitor_inv,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, Functor.map_braiding, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_rightUnitor, Category.assoc] at h'
  simp only [whiskerLeft_comp, Category.assoc]
  simpa using h'

/-- Transport of the second zigzag identity along a braided strong monoidal functor. -/
theorem Z2_map {D V : C} {c : 𝟙_ C ⟶ D ⊗ V} {ev : D ⊗ V ⟶ 𝟙_ C} (h : Z2 c ev) :
    Z2 (ε F ≫ F.map c ≫ δ F D V) (μ F D V ≫ F.map ev ≫ η F) := by
  unfold Z2 at h ⊢
  have h' := congrArg F.map h
  simp only [Functor.map_comp, Functor.map_id, Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, Functor.map_braiding, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_leftUnitor, Category.assoc] at h'
  simp only [comp_whiskerRight, Category.assoc]
  simpa using h'

end Transport

end CategoryTheory.MonoidalCategory.Zigzag
