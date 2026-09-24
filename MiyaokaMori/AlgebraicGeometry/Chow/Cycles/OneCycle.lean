import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme

/-! # One-cycles

The group of one-cycles `Z_1(X)` and the fundamental class `[C] ∈ Z_1(C)` of a smooth projective
curve `C` itself (the class `[C]` in Theorem 1.1 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The group of one-cycles `Z_1(X)` of a variety `X`. -/
abbrev OneCycle {k : Type u} [Field k] (X : Variety k) : Type u := ↥(CycleGroup X 1)

/-- The fundamental class `[C] ∈ Z_1(C)` of a smooth projective curve `C`. -/
noncomputable def SmoothProjectiveCurve.cycleClass {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) : OneCycle C.toVariety :=
  haveI : AlgebraicGeometry.IsNoetherian C.toVariety.toScheme := C.toVariety.isNoetherian
  AlgebraicGeometry.Intersection.dimensionFundamentalCycle C.toVariety.toScheme 1

end
