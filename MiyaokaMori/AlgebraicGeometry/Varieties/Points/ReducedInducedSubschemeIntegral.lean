import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme

/-! # The reduced closure of a point is integral

The closure of a point with its reduced induced structure (the closed subscheme of Mathlib's
`vanishingIdeal`) is an integral scheme whose generic point maps to the point (the reduced induced
closed subscheme of Stacks 01J3; reduced and irreducible implies integral).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `AlgebraicGeometry.Intersection.ReducedPointClosure.scheme X x` and `X.pointClosure x` have literally the
   same definition (`(IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme`), so
   the instances there apply here. -/

/-- The reduced closure of a point is an integral scheme. -/
theorem AlgebraicGeometry.Scheme.isIntegral_pointClosure {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    AlgebraicGeometry.IsIntegral (X.pointClosure x) :=
  AlgebraicGeometry.Intersection.ReducedPointClosure.scheme_isIntegral X x

attribute [instance] AlgebraicGeometry.Scheme.isIntegral_pointClosure

/-- The generic point of the reduced closure of `x` maps to `x`. -/
theorem AlgebraicGeometry.Scheme.pointClosureι_genericPoint {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    (X.pointClosureι x).base (genericPoint (X.pointClosure x)) = x := by
  have h : genericPoint (X.pointClosure x) =
      AlgebraicGeometry.Intersection.ReducedPointClosure.generic X x :=
    (genericPoint_spec _).eq (AlgebraicGeometry.Intersection.ReducedPointClosure.generic_spec X x)
  rw [h]
  rfl

end
