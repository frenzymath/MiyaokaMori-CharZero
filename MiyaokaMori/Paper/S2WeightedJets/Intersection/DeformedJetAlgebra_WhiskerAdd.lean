import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Extensionality for morphisms out of a whiskered biproduct

**Extensionality for morphisms out of `(⨁ F) ⊗ N` and `N ⊗ ⨁ F` in `X.Modules`**: such a morphism is determined by
its composites with the biproduct injections `biproduct.ι F j ▷ N` (resp. `N ◁ biproduct.ι F j`).

Proof: `𝟙 (⨁ F) = ∑ π_j ≫ ι_j` (`biproduct.total`) and whiskering is additive
(`MonoidalPreadditive X.Modules`, `AlgebraicGeometry.Scheme.Modules.monoidalPreadditive`, used locally via `letI`,
not as a global instance), so `g = ∑ (π_j ▷ N) ≫ (ι_j ▷ N) ≫ g`.

Source: Stacks 01CD (tensor product of sheaves of modules is additive in each variable). Used by
`reesDeformation.mul_condition` and `irrelevantPow_mul_condition` to reduce a statement about the image of
`biproduct.desc` to its components.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- A morphism out of `(⨁ F) ⊗ N` is determined by its composites with `biproduct.ι F j ▷ N`:
`𝟙 (⨁ F) = ∑ π_j ≫ ι_j` (`biproduct.total`), and `▷ N` is additive (`monoidalPreadditive`). -/
theorem AlgebraicGeometry.Scheme.Modules.biproduct_whiskerRight_hom_ext {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type} [Fintype J] (F : J → X.Modules) (N : X.Modules) {Z : X.Modules}
    (g h : CategoryTheory.Limits.biproduct F ⊗ N ⟶ Z)
    (w : ∀ j, (CategoryTheory.Limits.biproduct.ι F j ▷ N) ≫ g =
      (CategoryTheory.Limits.biproduct.ι F j ▷ N) ≫ h) : g = h := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  have htot : CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.biproduct F ⊗ N) =
      ∑ j : J, (CategoryTheory.Limits.biproduct.π F j ▷ N) ≫ (CategoryTheory.Limits.biproduct.ι F j ▷ N) := by
    rw [← CategoryTheory.MonoidalCategory.id_whiskerRight, ← CategoryTheory.Limits.biproduct.total,
      CategoryTheory.sum_whiskerRight]
    simp only [CategoryTheory.MonoidalCategory.comp_whiskerRight]
  calc g = CategoryTheory.CategoryStruct.id _ ≫ g := (Category.id_comp g).symm
    _ = ∑ j : J, (CategoryTheory.Limits.biproduct.π F j ▷ N) ≫
        ((CategoryTheory.Limits.biproduct.ι F j ▷ N) ≫ g) := by
      rw [htot, Preadditive.sum_comp]
      simp only [Category.assoc]
    _ = ∑ j : J, (CategoryTheory.Limits.biproduct.π F j ▷ N) ≫
        ((CategoryTheory.Limits.biproduct.ι F j ▷ N) ≫ h) := by
      exact Finset.sum_congr rfl fun j _ => by rw [w j]
    _ = CategoryTheory.CategoryStruct.id _ ≫ h := by
      rw [htot, Preadditive.sum_comp]
      simp only [Category.assoc]
    _ = h := Category.id_comp h

/-- A morphism out of `N ⊗ ⨁ F` is determined by its composites with `N ◁ biproduct.ι F j`. -/
theorem AlgebraicGeometry.Scheme.Modules.biproduct_whiskerLeft_hom_ext {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type} [Fintype J] (N : X.Modules) (F : J → X.Modules) {Z : X.Modules}
    (g h : N ⊗ CategoryTheory.Limits.biproduct F ⟶ Z)
    (w : ∀ j, (N ◁ CategoryTheory.Limits.biproduct.ι F j) ≫ g =
      (N ◁ CategoryTheory.Limits.biproduct.ι F j) ≫ h) : g = h := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  have htot : CategoryTheory.CategoryStruct.id (N ⊗ CategoryTheory.Limits.biproduct F) =
      ∑ j : J, (N ◁ CategoryTheory.Limits.biproduct.π F j) ≫ (N ◁ CategoryTheory.Limits.biproduct.ι F j) := by
    rw [← CategoryTheory.MonoidalCategory.whiskerLeft_id, ← CategoryTheory.Limits.biproduct.total,
      CategoryTheory.whiskerLeft_sum]
    simp only [CategoryTheory.MonoidalCategory.whiskerLeft_comp]
  calc g = CategoryTheory.CategoryStruct.id _ ≫ g := (Category.id_comp g).symm
    _ = ∑ j : J, (N ◁ CategoryTheory.Limits.biproduct.π F j) ≫
        ((N ◁ CategoryTheory.Limits.biproduct.ι F j) ≫ g) := by
      rw [htot, Preadditive.sum_comp]
      simp only [Category.assoc]
    _ = ∑ j : J, (N ◁ CategoryTheory.Limits.biproduct.π F j) ≫
        ((N ◁ CategoryTheory.Limits.biproduct.ι F j) ≫ h) := by
      exact Finset.sum_congr rfl fun j _ => by rw [w j]
    _ = CategoryTheory.CategoryStruct.id _ ≫ h := by
      rw [htot, Preadditive.sum_comp]
      simp only [Category.assoc]
    _ = h := Category.id_comp h

end
