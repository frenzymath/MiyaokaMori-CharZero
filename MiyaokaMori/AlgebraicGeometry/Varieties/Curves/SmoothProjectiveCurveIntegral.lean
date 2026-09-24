import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SpecNormalOfIntegrallyClosed
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks033m

/-! # A smooth connected projective curve is integral

A smooth connected projective curve over a field is an integral scheme (smooth implies normal, a
Noetherian normal scheme is a finite disjoint union of normal integral components, and connected
then implies integral).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A smooth connected projective curve is integral; an alias of the instance
`SmoothProjectiveCurve.isIntegral` (in dimension one the stalks are computed directly, see
`SmoothOverFieldDimLeOneNormal`). -/
theorem SmoothProjectiveCurve.isIntegral_of_smooth_connected {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsIntegral C.toScheme :=
  SmoothProjectiveCurve.isIntegral C

end
