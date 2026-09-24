import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurveOnCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CurveDegreeIntersectionCompat
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassLemmas
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.NumericalEquivalence
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor

/-! # Numerical equivalence of divisors on a curve is equality of degrees

Two divisors on a smooth projective curve are numerically equivalent if and only if they have the
same degree; in particular any two closed points satisfy `[y] ≡ [z]` (§4 of the paper, proof of
Lemma 5.1).

Route: every integral curve `Γ` on `C` has `Set.range Γ.ι.base = univ`
(`IntegralCurve.range_eq_univ_of_curve`), so the image of its generic point is the generic point of
`C` and `[Γ] = [C]` as cycles (both are the one-point cycle `single η 1`); hence
`D ⬝ [Γ] = D ⬝ [C] = deg D` by `intersectionNumber_curve_eq_degree`. Taking `Γ = C` itself
(identity closed immersion) gives the forward direction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `C` itself, via the identity closed immersion, as an integral curve on `C`. -/
noncomputable def SmoothProjectiveCurve.selfIntegralCurve {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) : IntegralCurve k C.toScheme :=
  IntegralCurve.ofClosedSubvariety C.isProper (ClosedSubvariety.self C.toVariety) C.dim_one

/-- The image of the generic point of an integral curve `Γ` on a smooth projective curve `C` is the
generic point of `C`: `Γ.ι` has full range, so `closure {ι η_Γ} ⊇ ι(closure {η_Γ}) = range ι = C`. -/
theorem IntegralCurve.image_genericPoint_of_curve {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (Γ : IntegralCurve k C.toScheme) :
    Γ.ι.base (genericPoint Γ.carrier) = genericPoint C.toScheme := by
  have hΓ : closure ({genericPoint Γ.carrier} : Set Γ.carrier) = Set.univ :=
    (genericPoint_spec Γ.carrier).def
  have hsub : Set.univ ⊆ closure ({Γ.ι.base (genericPoint Γ.carrier)} : Set C.toScheme) := by
    calc Set.univ = Set.range Γ.ι.base := (IntegralCurve.range_eq_univ_of_curve C Γ).symm
      _ = Γ.ι.base '' closure ({genericPoint Γ.carrier} : Set Γ.carrier) := by
          rw [hΓ, Set.image_univ]
      _ ⊆ closure (Γ.ι.base '' ({genericPoint Γ.carrier} : Set Γ.carrier)) :=
          image_closure_subset_closure_image Γ.ι.continuous
      _ = closure ({Γ.ι.base (genericPoint Γ.carrier)} : Set C.toScheme) := by
          rw [Set.image_singleton]
  have hgen : IsGenericPoint (Γ.ι.base (genericPoint Γ.carrier)) (⊤ : Set C.toScheme) :=
    Set.eq_univ_of_univ_subset hsub
  exact hgen.eq (genericPoint_spec C.toScheme)

private theorem coe_cast_cycleGroup {k : Type u} [Field k] {X : Variety k}
    {i j : ℕ} (h : i = j) (c : CycleGroup X i) :
    ((cast (congrArg (fun n : ℕ => ↥(CycleGroup X n)) h) c : CycleGroup X j) :
      AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) = c.1 := by
  cases h
  rfl

open Classical in
/-- `[C]` as a cycle is the one-point cycle at the generic point (same computation as in
`intersectionNumber_curve_eq_lineBundle_degree`). -/
theorem SmoothProjectiveCurve.cycleClass_coe_eq_single {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) :
    (C.cycleClass : AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) =
      Function.locallyFinsuppWithin.single (genericPoint C.toScheme) (1 : ℤ) := by
  have hdim : C.toScheme.dimension = 1 := by
    unfold AlgebraicGeometry.Scheme.dimension
    rw [C.dim_one]
    simp
  have : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hfund := congrFun (C.toScheme.fundamentalCycle_of_isIntegral
    (MiyaokaMori.TopSelfIntersectionCurve.topologicalKrullDim_ne_top_of_dimension
      Nat.one_pos hdim))
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
/-- On a smooth projective curve `C`, every integral curve `Γ ⊂ C` has fundamental class `[C]`. -/
theorem IntegralCurve.fundamentalClass_eq_cycleClass {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (Γ : IntegralCurve k C.toVariety.toScheme) :
    Γ.fundamentalClass = C.cycleClass := by
  apply Subtype.ext
  rw [SmoothProjectiveCurve.cycleClass_coe_eq_single]
  unfold IntegralCurve.fundamentalClass
  rw [coe_cast_cycleGroup Γ.dimension_eq_one,
    ClosedSubvariety.fundamentalClass_eq_single Γ.toClosedSubvariety]
  change Function.locallyFinsuppWithin.single (Γ.ι.base (genericPoint Γ.carrier)) (1 : ℤ) = _
  rw [IntegralCurve.image_genericPoint_of_curve C Γ]

/-- `D ⬝ [Γ] = deg D` for every integral curve `Γ` on the smooth projective curve `C`. -/
theorem intersectionNumber_integralCurve_eq_degree {k : Type u} [Field k] [IsAlgClosed k]
    (C : SmoothProjectiveCurve k) (D : CartierDivisor C.toVariety)
    (Γ : IntegralCurve k C.toVariety.toScheme) :
    intersectionNumber C.toSmoothProjectiveVariety D Γ.fundamentalClass =
      CartierDivisor.degree C D := by
  rw [IntegralCurve.fundamentalClass_eq_cycleClass C Γ]
  exact intersectionNumber_curve_eq_degree C D

theorem numEquiv_iff_degree_eq {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (D E : CartierDivisor C.toVariety) :
    NumEquivDivisor (X := C.toSmoothProjectiveVariety) D E ↔
      CartierDivisor.degree C D = CartierDivisor.degree C E := by
  constructor
  · intro h
    exact (intersectionNumber_integralCurve_eq_degree C D C.selfIntegralCurve).symm.trans
      ((h C.selfIntegralCurve).trans
        (intersectionNumber_integralCurve_eq_degree C E C.selfIntegralCurve))
  · intro h Γ
    exact (intersectionNumber_integralCurve_eq_degree C D Γ).trans
      (h.trans (intersectionNumber_integralCurve_eq_degree C E Γ).symm)

theorem points_numEquiv {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (y z : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) (hz : IsClosed ({z} : Set C.toScheme)) :
    NumEquivDivisor (X := C.toSmoothProjectiveVariety) (Divisor.ofPoint y) (Divisor.ofPoint z) := by
  apply (numEquiv_iff_degree_eq (Divisor.ofPoint y) (Divisor.ofPoint z)).2
  rw [Divisor.ofPoint_degree y hy, Divisor.ofPoint_degree z hz]

end
