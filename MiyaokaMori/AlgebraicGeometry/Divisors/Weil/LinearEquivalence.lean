import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.Divisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisorAdditive
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.SchemePrincipalWeilDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor

/-! # Linear equivalence of Weil divisors

`D ~ D'` iff `D − D'` is the principal divisor of a nonzero rational function.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Linear equivalence: `D − D'` is the principal divisor of some nonzero rational function. -/
def AlgebraicGeometry.Scheme.LinearlyEquivalent {X : AlgebraicGeometry.Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (D D' : X.WeilDivisor) : Prop :=
  ∃ f : X.functionField, f ≠ 0 ∧ D - D' = X.principalDivisor f

end
