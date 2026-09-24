import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPreservesColimits
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow

/-! # The monoidal structure on `X.Modules` is preadditive

The monoidal structure on `X.Modules` is bilinear with respect to the preadditive structure
(Mathlib's `MonoidalPreadditive`): `X ◁ (f + g) = X ◁ f + X ◁ g`, `X ◁ 0 = 0`, and likewise for right
whiskering; consequently the tensor product distributes over finite biproducts (Mathlib's
`leftDistributor` / `rightDistributor` / `whiskerLeft_sum` become available).

Proof: `tensorLeft N` and `tensorRight N` preserve colimits (`ModulesTensorPreservesColimits`:
sheafification is a monoidal localization and `⊗` is a left adjoint), in particular binary
coproducts, hence binary biproducts (`preservesBinaryBiproducts_of_preservesBinaryCoproducts`), hence
they are additive (`Functor.additive_of_preservesBinaryBiproducts`; zero morphisms are preserved since
initial objects are). The four fields of `MonoidalPreadditive` are `(tensorLeft N).map_zero / map_add`
and `(tensorRight N).map_zero / map_add`.

This is **not** registered as a global instance: at a use site write
`haveI := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X`.

Source: standard (a left adjoint between additive categories is additive; the categorical skeleton
of Stacks 01CE).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `N ⊗ (-)` is an additive functor. -/
theorem tensorLeft_additive (N : X.Modules) : (tensorLeft N).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft N) := preservesColimitsOfSize_shrink _
  have : PreservesBinaryBiproducts (tensorLeft N) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- `(-) ⊗ N` is an additive functor. -/
theorem tensorRight_additive (N : X.Modules) : (tensorRight N).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (tensorRight N) := preservesColimitsOfSize_shrink _
  have : PreservesBinaryBiproducts (tensorRight N) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Left whiskering preserves zero. -/
theorem whiskerLeft_zero' (P : X.Modules) {Y Z : X.Modules} : P ◁ (0 : Y ⟶ Z) = 0 := by
  have := tensorLeft_additive P
  exact (tensorLeft P).map_zero Y Z

/-- Right whiskering preserves zero. -/
theorem zero_whiskerRight' {Y Z : X.Modules} (P : X.Modules) : (0 : Y ⟶ Z) ▷ P = 0 := by
  have := tensorRight_additive P
  exact (tensorRight P).map_zero Y Z

/-- Left whiskering preserves addition. -/
theorem whiskerLeft_add' (P : X.Modules) {Y Z : X.Modules} (f g : Y ⟶ Z) :
    P ◁ (f + g) = P ◁ f + P ◁ g := by
  have := tensorLeft_additive P
  exact (tensorLeft P).map_add

/-- Right whiskering preserves addition. -/
theorem add_whiskerRight' {Y Z : X.Modules} (f g : Y ⟶ Z) (P : X.Modules) :
    (f + g) ▷ P = f ▷ P + g ▷ P := by
  have := tensorRight_additive P
  exact (tensorRight P).map_add

/-- The monoidal structure on `X.Modules` is preadditive (**not a global instance**; use `haveI`). -/
theorem monoidalPreadditive (X : AlgebraicGeometry.Scheme.{u}) : MonoidalPreadditive X.Modules where
  whiskerLeft_zero := whiskerLeft_zero' _
  zero_whiskerRight := zero_whiskerRight' _
  whiskerLeft_add := whiskerLeft_add' _
  add_whiskerRight := fun f g => add_whiskerRight' f g _

end AlgebraicGeometry.Scheme.Modules
