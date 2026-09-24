import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition

/-! # Multiplicativity of the function field degree

If `f : X ⟶ Y` sends the generic point to the generic point, then for integral schemes
`functionFieldDegree (f ≫ g) = functionFieldDegree f * functionFieldDegree g`.

Proof sketch: apply `AlgebraicGeometry.Intersection.residueDegree_comp` at the generic point of `X`,
rewrite the residue degree at the intermediate point as `functionFieldDegree g` using the
hypothesis on the generic point, and reorder the factors.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The function field degree is multiplicative in a composite `f ≫ g` when `f` sends the generic
point to the generic point. -/
theorem functionFieldDegree_comp_of_genericPoint
    {X Y Z : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : f.base (genericPoint X) = genericPoint Y) :
    functionFieldDegree (f ≫ g) = functionFieldDegree f * functionFieldDegree g := by
  unfold functionFieldDegree
  rw [AlgebraicGeometry.Intersection.residueDegree_comp]
  rw [hf]
  exact Nat.mul_comm _ _

end
