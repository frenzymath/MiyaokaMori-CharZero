import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso

/-! # The structure sheaf is a unit for the tensor product

The structure sheaf is a unit for `Scheme.Modules.tensor`: for every `O_X`-module `M` on `X` there
are canonical isomorphisms `tensor O_X M ≅ M` and `tensor M O_X ≅ M` (`unitTensorIso` /
`tensorUnitIso`).

Proof:
1. `Modules.tensor A B` (the sheafification of the sectionwise tensor presheaf) is canonically
   isomorphic to the monoidal `A ⊗ B` of `X.Modules`: `Modules.tensorIsoTensorObj`.
2. The monoidal unit `𝟙_ X.Modules` (of the localized monoidal structure) and
   `SheafOfModules.unit X.ringCatSheaf` are literally the same after unfolding all definitions, so
   `eqToIso (by with_unfolding_all rfl)` passes between them (as in `Modules.unitTensorPowIso`; no
   choice is involved).
3. Compose with the left/right unitors `λ_ M`, `ρ_ M` of the monoidal category.

Source: Stacks 01CA (`O_X ⊗_{O_X} F = F`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `SheafOfModules.unit` is literally the monoidal unit of `X.Modules`. -/
theorem AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit (X : AlgebraicGeometry.Scheme.{u}) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) =
      CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules := by
  with_unfolding_all rfl

/-- Left unit law: `O_X ⊗ M ≅ M`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.unitTensorIso {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit X.ringCatSheaf) M ≅ M :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ M ≪≫
    CategoryTheory.MonoidalCategory.whiskerRightIso (C := X.Modules)
      (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) M ≪≫
    CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules) M

/-- Right unit law: `M ⊗ O_X ≅ M`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorUnitIso {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M _ ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso (C := X.Modules) M
      (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) ≪≫
    CategoryTheory.MonoidalCategoryStruct.rightUnitor (C := X.Modules) M

end
