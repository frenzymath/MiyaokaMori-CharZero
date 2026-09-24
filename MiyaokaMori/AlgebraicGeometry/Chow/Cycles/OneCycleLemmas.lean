import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassLemmas
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle

/-! # Lemmas on the fundamental one-cycle of a smooth projective curve

The cycle class `[C] ∈ Z_1(C)` of a smooth projective curve is the single point cycle at its
generic point and agrees with the fundamental class of the scheme; separated from the definition of
`OneCycle`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open Classical in
theorem SmoothProjectiveCurve.cycleClass_eq_single {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) :
    (C.cycleClass : AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) =
      Function.locallyFinsuppWithin.single (genericPoint C.toVariety.toScheme) (1 : ℤ) := by
  have hdim : C.toScheme.dimension = 1 := by
    unfold AlgebraicGeometry.Scheme.dimension
    rw [C.dim_one]
    simp
  have hne : topologicalKrullDim C.toScheme ≠ ⊤ := by
    rw [C.dim_one]
    decide
  have : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hfund := congrFun (C.toScheme.fundamentalCycle_of_isIntegral hne)
  rw [hdim] at hfund
  ext x
  have hx : (C.cycleClass : AlgebraicGeometry.AlgebraicCycle C.toScheme ℤ) x =
      C.toScheme.fundamentalCycle 1 x := by
    have : AlgebraicGeometry.IsNoetherian C.toVariety.toScheme := C.toVariety.isNoetherian
    refine (AlgebraicGeometry.Intersection.dimensionFundamentalCycle_apply C.toVariety.toScheme 1 x).trans ?_
    rfl
  rw [hx, hfund x]
  simp [Function.locallyFinsuppWithin.single_apply]

open Classical in
theorem SmoothProjectiveCurve.genericPoint_mem_oneCycle {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) :
    Function.locallyFinsuppWithin.single (genericPoint C.toVariety.toScheme) (1 : ℤ) ∈
      CycleGroup C.toVariety 1 := by
  rw [← SmoothProjectiveCurve.cycleClass_eq_single]
  exact C.cycleClass.2

theorem SmoothProjectiveCurve.cycleClass_eq_fundamentalClass {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) :
    (C.cycleClass : AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ)
      = ((ClosedSubvariety.self C.toVariety).fundamentalClass :
          AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) := by
  rw [SmoothProjectiveCurve.cycleClass_eq_single,
    ClosedSubvariety.fundamentalClass_eq_single (ClosedSubvariety.self C.toVariety)]
  rfl

end
