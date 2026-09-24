import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors

/-! # A smooth projective curve as a smooth projective variety

A smooth projective curve `C` is a smooth projective variety: the underlying variety is
`C.toVariety`, and the fields smooth, projective and connected are those of `C` (the fields of
`SmoothProjectiveVariety` are the same conditions on the carrier, and
`C.toVariety.carrier = C.carrier` holds by definition). `P¹` as a smooth projective variety is
`ProjectiveLine.asSmoothProjectiveCurve k` followed by this construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A smooth projective curve regarded as a smooth projective variety (same underlying scheme). -/

noncomputable def SmoothProjectiveCurve.toSmoothProjectiveVariety {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) : SmoothProjectiveVariety k where
  toVariety := C.toVariety
  smooth := C.smooth
  projective := C.projective
  connected := C.connected

theorem SmoothProjectiveCurve.toSmoothProjectiveVariety_toVariety {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) : C.toSmoothProjectiveVariety.toVariety = C.toVariety := rfl

/-- `P¹` as a smooth projective variety. -/

noncomputable abbrev ProjectiveLine.asSmoothProjectiveVariety (k : Type u) [Field k] :
    SmoothProjectiveVariety k :=
  (ProjectiveLine.asSmoothProjectiveCurve k).toSmoothProjectiveVariety

end
