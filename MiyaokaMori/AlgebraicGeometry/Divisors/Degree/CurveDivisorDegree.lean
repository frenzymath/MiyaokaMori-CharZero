import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil

/-! # Degree of a divisor on a smooth projective curve

The degree of a Cartier divisor on a smooth projective curve, `deg D = Σ_x n_x · [κ(x) : k]` (the
support is finite; the sum is a `finsum`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree of a Cartier divisor `D` on a smooth projective curve: the degree
`AlgebraicGeometry.AlgebraicCycle.degree` of its Weil cycle, `Σ_x n_x · [κ(x) : k]`, where
`[κ(x) : k]` is Mathlib's `residueDegree`. Properness of the curve does not enter the definition
(`finsum` does not need it); it is used only in the theorems. -/
noncomputable def CartierDivisor.degree {k : Type u} [Field k] (C : SmoothProjectiveCurve k)
    (D : CartierDivisor C.toVariety) : ℤ :=
  AlgebraicGeometry.AlgebraicCycle.degree (k := k)
    (CartierDivisor.weilCycle C.toVariety D : AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ)

/-- By definition, the degree of a divisor is the degree of its Weil cycle. -/
theorem CartierDivisor.degree_weilCycle {k : Type u} [Field k] (C : SmoothProjectiveCurve k)
    (D : CartierDivisor C.toVariety) :
    CartierDivisor.degree C D =
      AlgebraicGeometry.AlgebraicCycle.degree (k := k)
        (CartierDivisor.weilCycle C.toVariety D :
          AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) := rfl

end
