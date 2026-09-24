import MiyaokaMori.Prelude

/-! # Closed points

A closed point `x` of a scheme `X`: the singleton `{x}` is closed in the underlying space (in the
paper, "point" always means closed point).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `x` is a closed point of `X`. -/
def IsClosedPointOf (X : AlgebraicGeometry.Scheme.{u}) (x : X) : Prop :=
  IsClosed ({x} : Set X)   -- equivalently, `x ∈ closedPoints X`

end
