import MiyaokaMori.AlgebraicGeometry.Divisors.CodimensionOneFinite

/-! # Finitely many codimension-one points outside an open

For a Noetherian integral scheme `X` and a nonempty open `U ⊆ X`, only finitely many points of
codimension one lie outside `U`: they are among the generic points of the irreducible components of
`X ∖ U`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.finite_coheight_one_not_mem {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (U : X.Opens) [Nonempty U] :
    {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  simpa [and_comm] using AlgebraicGeometry.Divisors.finite_codimensionOneOutside X U

end
