import MiyaokaMori.Prelude

/-! # Prime divisors

A prime divisor is an irreducible closed subvariety of codimension one of `X`; encoded by its generic point,
it is a point of coheight `1`. The two encodings correspond by the bijection of sober spaces.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A point `Z` of `X` is a prime divisor if it has coheight `1`. -/
def AlgebraicGeometry.Scheme.IsPrimeDivisor {X : AlgebraicGeometry.Scheme.{u}} (Z : X) : Prop :=
  Order.coheight Z = 1

/-- Equivalence with the encoding as irreducible closed subsets of codimension one. -/
noncomputable def AlgebraicGeometry.Scheme.primeDivisorEquivIrreducibleCloseds (X : AlgebraicGeometry.Scheme.{u}) :
    {Z : X // X.IsPrimeDivisor Z} ≃
      {C : TopologicalSpace.IrreducibleCloseds X //
        Order.coheight (irreducibleSetEquivPoints C) = 1} :=
  (Equiv.subtypeEquiv (irreducibleSetEquivPoints (α := X)).toEquiv (fun _ => Iff.rfl)).symm

end
