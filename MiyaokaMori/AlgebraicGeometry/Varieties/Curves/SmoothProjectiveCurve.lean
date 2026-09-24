import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ConnectedScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # Smooth projective curves

A smooth connected projective curve `C` over `k`: a `k`-scheme with structure morphism
`C → Spec k` which is smooth, projective over `k`, with connected underlying space and of
dimension `1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A smooth connected projective curve over `k`. -/
structure SmoothProjectiveCurve (k : Type u) [Field k] where
  carrier : AlgebraicGeometry.Scheme.{u}
  [«over» : carrier.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  smooth : IsSmoothOver k carrier
  projective : IsProjectiveOver k carrier
  connected : ConnectedSpace carrier
  dim_one : SchemeIsOneDimensional carrier

attribute [instance] SmoothProjectiveCurve.over

end
