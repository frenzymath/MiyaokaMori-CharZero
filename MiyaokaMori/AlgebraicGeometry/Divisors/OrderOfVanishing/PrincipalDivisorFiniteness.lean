import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrimeDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdFiniteOnNoetherianOpen

/-! # Finiteness of the principal divisor

On a Noetherian integral scheme, for a fixed `0 ≠ f ∈ K(X)` only finitely many prime divisors `Z` have
`ord_Z(f) ≠ 0`, so that `div(f)` is a divisor. This is the case `V = ⊤` of
`AlgebraicGeometry.Scheme.finite_ord_ne_zero_inter_opens` (`OrdFiniteOnNoetherianOpen`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Only finitely many prime divisors have nonzero order of vanishing of a fixed rational function. -/
theorem AlgebraicGeometry.Scheme.finite_ord_ne_zero {X : AlgebraicGeometry.Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X.functionField} (hf : f ≠ 0) :
    {Z : X | X.IsPrimeDivisor Z ∧ X.ord f Z ≠ 0}.Finite := by
  letI : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  exact (AlgebraicGeometry.Divisors.finite_support_ord X f hf).subset fun Z hZ => hZ.2

end
