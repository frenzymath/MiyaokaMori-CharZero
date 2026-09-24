import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors

/-! # Smooth projective curves are locally Noetherian

The underlying scheme of a smooth projective curve is locally Noetherian (finite type over `k`
implies locally Noetherian), registered as an instance so that `Scheme.ord` and the function
field constructions apply directly to `C.toScheme`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance SmoothProjectiveCurve.isLocallyNoetherian {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsLocallyNoetherian C.carrier :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

end
