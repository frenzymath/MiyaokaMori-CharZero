import MiyaokaMori.Prelude

/-! # A section of a separated morphism is a closed immersion

For a section `σ` (`σ ≫ g = 𝟙`), first `σ ≫ g` is a closed immersion (an isomorphism), then
Mathlib's `IsClosedImmersion.of_comp` applies.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.IsClosedImmersion.of_section {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) [AlgebraicGeometry.IsSeparated g] (σ : X ⟶ Y)
    (hσ : σ ≫ g = CategoryTheory.CategoryStruct.id X) :
    AlgebraicGeometry.IsClosedImmersion σ := by
  haveI : AlgebraicGeometry.IsClosedImmersion (σ ≫ g) := by rw [hσ]; infer_instance
  exact AlgebraicGeometry.IsClosedImmersion.of_comp σ g

end
