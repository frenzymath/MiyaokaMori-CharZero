import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.Divisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrimeDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrincipalDivisorFiniteness
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor

/-! # Principal Weil divisors on a scheme

The principal Weil divisor `div(f) = Σ_Z ord_Z(f)·Z ∈ Div(X)` on a Noetherian integral scheme (`0` for
`f = 0`); this is the `X.principalDivisor` used by linear equivalence and the divisor class group.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open Classical in
/-- `div(f)`: the principal cycle `X.principalCycle` (with coefficients Mathlib's `Scheme.ord`) has finite
support on a Noetherian scheme (`principalCycle_support_finite`); repackage the codimension-one points of
its support as a Weil divisor in `FreeAbelianGroup` form. For `f = 0` the divisor is `0`. Noetherian means
locally Noetherian and quasi-compact. -/
noncomputable def AlgebraicGeometry.Scheme.principalDivisor (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionField) : X.WeilDivisor :=
  haveI : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  if hf : f = 0 then 0 else
    let c := X.principalCycle (Units.mk0 f hf)
    have hc : (Function.support c).Finite := X.principalCycle_support_finite (Units.mk0 f hf)
    ∑ Z ∈ hc.toFinset, if hZ : X.IsPrimeDivisor Z then c Z • FreeAbelianGroup.of ⟨Z, hZ⟩ else 0

end
