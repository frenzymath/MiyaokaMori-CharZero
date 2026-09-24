import MiyaokaMori.Prelude

/-! # The closure of a point as a reduced closed subscheme

The closure `closure {x}` of a point `x` of a scheme `X` with its reduced induced closed subscheme
structure: `pointClosure x := (vanishingIdeal (closure {x})).subscheme`, with `pointClosureι x` its
closed immersion into `X` (Mathlib's `IdealSheafData.subschemeι`). The generators of the cycle
groups ("integral closed subschemes = closures of points") are encoded with it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The closure of the point `x` with its reduced induced structure (the `subscheme` of Mathlib's
`vanishingIdeal`). -/

noncomputable def AlgebraicGeometry.Scheme.pointClosure {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    AlgebraicGeometry.Scheme.{u} :=
  (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme

/-- The closed immersion of the reduced closure of `x` into `X`. -/
noncomputable def AlgebraicGeometry.Scheme.pointClosureι {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    X.pointClosure x ⟶ X :=
  (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subschemeι

end
