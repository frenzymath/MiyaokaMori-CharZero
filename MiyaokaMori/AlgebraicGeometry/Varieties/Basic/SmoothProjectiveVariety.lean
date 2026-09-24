import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ConnectedScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # Smooth projective varieties

The central object of the main theorem: a smooth, projective, connected variety over `k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A smooth projective variety over `k`: a variety which is smooth and projective over `k` and
connected. -/
structure SmoothProjectiveVariety (k : Type u) [Field k] extends Variety k where
  smooth : IsSmoothOver k carrier
  projective : IsProjectiveOver k carrier
  connected : ConnectedSpace carrier.carrier

end
