import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveAsSmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.Paper.S1Intro.BaseField
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.Stacks0az2
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeEqCartierDivisorDegree

/-! # Compatibility of the intersection number with the degree on a curve

On a smooth projective curve, the intersection number of Fulton's route is compatible with the
degree of divisors and line bundles: `D · [C] = deg D = deg O_C(D)` (Theorem 1.1 of the paper,
where `-K_X · f_*[C] = deg f^*T_X`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Route: the line bundle version is proved first. `[C]` is the cycle with coefficient `1` at the generic
   point, so `capDivisor_single` (with `v = η`) and the generic-point comparison of caps
   (`FirstChernCapPointGeneric.lean`) replace `ι_* div_{ι^*O(D)}(s)` by `div_{O(D)}(s′)`; taking degrees
   (`ChowGroup.degree_mk`, Stacks 0AZ2) and using `topSelfIntersection_eq_degree_rationalSectionDivisor`
   together with `LineBundle.degree_eq_topSelfIntersection` gives the claim. The divisor version follows
   by `CartierDivisor.lineBundle_degree`. -/

open AlgebraicGeometry in
/-- `D · [C] = deg O_C(D)` on a smooth projective curve `C`. -/
theorem intersectionNumber_curve_eq_lineBundle_degree {k : Type*} [Field k] [IsAlgClosed k]
    (C : SmoothProjectiveCurve k) (D : CartierDivisor C.toVariety) :
    intersectionNumber C.toSmoothProjectiveVariety D C.cycleClass
      = LineBundle.degree (CartierDivisor.lineBundle D) := by
  classical
  have hdim : C.toScheme.dimension = 1 := by
    unfold AlgebraicGeometry.Scheme.dimension
    rw [C.dim_one]
    simp
  have hproper : IsProperOver k C.toScheme :=
    ((isProjectiveOver_iff_isProper_and_isAmple k C.carrier).mp C.projective).1
  haveI : IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  haveI : IsLocallyNoetherian C.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (C.toScheme ↘ Spec (CommRingCat.of k))
  haveI : IsLocallyNoetherian (C.toScheme.pointClosure (genericPoint C.toScheme)) :=
    Scheme.isLocallyNoetherian_pointClosure _
  let η : C.toScheme := genericPoint C.toScheme
  let L : C.toScheme.Modules := (CartierDivisor.lineBundle D).toModules
  have hLB : AlgebraicGeometry.Scheme.Modules.IsLineBundle L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hx, ⟨e⟩⟩ :=
      (LineBundle.toModules_isLineBundle (CartierDivisor.lineBundle D)).locally_trivial x
    exact ⟨U, hx, ⟨e⟩⟩
  letI : AlgebraicGeometry.Scheme.Modules.IsLineBundle L := hLB
  have hv : Order.height η = ((0 + 1 : ℕ) : ℕ∞) :=
    MiyaokaMori.TopSelfIntersectionCurve.height_genericPoint_of_dimension Nat.one_pos hdim
  have hkd : topologicalKrullDim C.toScheme ≤ 1 := by
    rw [C.dim_one]
  let Lw : (C.toScheme.pointClosure η).Modules :=
    (Scheme.Modules.pullback (C.toScheme.pointClosureι η)).obj L
  haveI hLwB : AlgebraicGeometry.Scheme.Modules.IsLineBundle Lw := by
    change AlgebraicGeometry.Scheme.Modules.IsLineBundle
      ((AlgebraicGeometry.Scheme.Modules.pullback (C.toScheme.pointClosureι η)).obj L)
    exact AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback
      (C.toScheme.pointClosureι η) L
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_stalk_genericPoint_ne_zero Lw
  obtain ⟨s', hs', hC⟩ :=
    @MiyaokaMori.FirstChernCapPointGeneric.properPushforward_pointClosure_rationalSectionDivisor
      _ _ _ _ L (inferInstance : AlgebraicGeometry.Scheme.Modules.IsLineBundle L) s hs
  have hmem' := MiyaokaMori.RationalSectionDegree.rationalSectionDivisor_mem_cycleSubgroup_zero
    hproper hkd L s' hs'
  have hmem : AlgebraicGeometry.AlgebraicCycle.properPushforward (ClosedSubvariety.ofPoint (X := C.toVariety) η).ι
      (Lw.rationalSectionDivisor s) ∈ CycleGroup C.toVariety 0 := by
    have : AlgebraicGeometry.AlgebraicCycle.properPushforward (ClosedSubvariety.ofPoint (X := C.toVariety) η).ι
        (Lw.rationalSectionDivisor s) = L.rationalSectionDivisor s' := hC
    rw [this]
    exact hmem'
  have hvmem : Function.locallyFinsuppWithin.single η (1 : ℤ) ∈ CycleGroup C.toVariety (0 + 1) := by
    intro x hx
    have hxη : x = η := by
      by_contra hne
      exact hx (by simp [Function.locallyFinsuppWithin.single_apply, hne])
    rw [hxη]
    exact hv
  have hfund := congrFun (C.toScheme.fundamentalCycle_of_isIntegral
    (MiyaokaMori.TopSelfIntersectionCurve.topologicalKrullDim_ne_top_of_dimension
      Nat.one_pos hdim))
  rw [hdim] at hfund
  have hcc : C.cycleClass = ⟨Function.locallyFinsuppWithin.single η 1, hvmem⟩ := by
    apply Subtype.ext
    ext x
    have hx : (C.cycleClass : AlgebraicCycle C.toScheme ℤ) x = C.toScheme.fundamentalCycle 1 x := by
      haveI : IsNoetherian C.toVariety.toScheme := C.toVariety.isNoetherian
      refine (AlgebraicGeometry.Intersection.dimensionFundamentalCycle_apply C.toVariety.toScheme 1 x).trans ?_
      rfl
    rw [hx, hfund x]
    simp [Function.locallyFinsuppWithin.single_apply, η]
  have h1 := capDivisor_single D 0 η hv hvmem s hs hmem
  -- deg O(D) = topSelfIntersection = deg div_L(s') (theorem-level interface)
  have hB : LineBundle.degree (CartierDivisor.lineBundle D) =
      AlgebraicCycle.degree (k := k) (L.rationalSectionDivisor s') := by
    rw [LineBundle.degree_eq_topSelfIntersection C hproper]
    exact MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_degree_rationalSectionDivisor
      hproper hdim L s' hs'
  have hval : intersectionNumber C.toSmoothProjectiveVariety D C.cycleClass =
      AlgebraicCycle.degree (k := k) (L.rationalSectionDivisor s') := by
    unfold intersectionNumber
    rw [hcc]
    refine (congrArg (ChowGroup.degree C.toSmoothProjectiveVariety) h1).trans ?_
    refine (ChowGroup.degree_mk C.toSmoothProjectiveVariety _).trans ?_
    unfold AlgebraicCycle.degree
    refine finsum_congr fun x => ?_
    have hCx := DFunLike.congr_fun hC x
    exact congrArg (· * _) hCx
  rw [hval, hB]

theorem intersectionNumber_curve_eq_degree {k : Type*} [Field k] [IsAlgClosed k]
    (C : SmoothProjectiveCurve k) (D : CartierDivisor C.toVariety) :
    intersectionNumber C.toSmoothProjectiveVariety D C.cycleClass
      = CartierDivisor.degree C D :=
  (intersectionNumber_curve_eq_lineBundle_degree C D).trans (CartierDivisor.lineBundle_degree C D)

end
