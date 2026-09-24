import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.LineBundleIsDivisorial
import MiyaokaMori.AlgebraicGeometry.Chow.CapCommutes
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapEffectiveEqDivisorCycle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CurveNumeqIffDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.DivisorToOneCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.FiberDivisorPullback
import MiyaokaMori.Paper.S4Completion.FiberOneCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntersectionLinear
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.NumericalEquivalence
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackPreservesNumeq
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.SurfaceIntersectionPairing
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycleSumOfIntegralCurves
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.ClIsoPic

/-! # All fibers of the ruled surface are numerically equivalent

All fibers of `π_S` are numerically equivalent to each other: points of `C̃` are numerically
equivalent and the fiber divisors are their pullbacks (§4 of the paper, proof of
Lemma 5.1). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem fibers_numEquiv {k : Type u} [Field k] [IsAlgClosed k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme)
    [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] (hπ : AlgebraicGeometry.Surjective π)
    (y z : C.toScheme) (hy : IsClosed {y}) (hz : IsClosed {z}) :
    (fiberCycle π hπ y).NumEquiv (fiberCycle π hπ z) := by
  have hover : π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := inferInstance
  let hproper : AlgebraicGeometry.IsProper π :=
    @isProper_of_projective k _ S.toSmoothProjectiveVariety
      C.toSmoothProjectiveVariety π hover
  have hdiv : NumEquivDivisor (fiberDivisor π hπ y) (fiberDivisor π hπ z) :=
    pullback_numEquiv π hπ.surj (points_numEquiv y z hy hz)
  intro L
  have hdivisor : ∃ D : CartierDivisor S.toVariety, Nonempty (D.lineBundle ≅ L) := by
    let X := S.toSmoothProjectiveVariety
    let P : PicardGroup S.toVariety := Quotient.mk _ L
    obtain ⟨c, hc⟩ := (classGroupEquivPicardGroup X).surjective P
    obtain ⟨W, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨D, rfl⟩ := (cartierWeilEquiv X).surjective W
    have hclass : (classGroupEquivPicardGroup X)
        (Multiplicative.ofAdd
          (QuotientAddGroup.mk ((cartierWeilEquiv X) D) : S.toScheme.ClassGroup)) = P := hc
    rw [classGroupEquivPicardGroup_mk X D] at hclass
    exact ⟨D, Quotient.exact hclass⟩
  obtain ⟨A, ⟨eA⟩⟩ := hdivisor
  let ZA : OneCycle S.toVariety :=
    SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸ A.weilCycle
  obtain ⟨s, hs⟩ := OneCycle.eq_sum_fundamentalClass ZA
  have hpair : surfaceIntersection S (fiberDivisor π hπ y) A =
      surfaceIntersection S (fiberDivisor π hπ z) A := by
    unfold surfaceIntersection
    change intersectionNumber S.toSmoothProjectiveVariety (fiberDivisor π hπ y) ZA =
      intersectionNumber S.toSmoothProjectiveVariety (fiberDivisor π hπ z) ZA
    rw [← CartierDivisor.lineBundle_inter, ← CartierDivisor.lineBundle_inter, hs,
      inter_sum, inter_sum]
    apply Finset.sum_congr rfl
    intro Gamma hGamma
    rw [CartierDivisor.lineBundle_inter, CartierDivisor.lineBundle_inter, hdiv Gamma]
  have hsymm : surfaceIntersection S A (fiberDivisor π hπ y) =
      surfaceIntersection S A (fiberDivisor π hπ z) :=
    (surfaceIntersection_comm S A (fiberDivisor π hπ y)).trans
      (hpair.trans (surfaceIntersection_comm S (fiberDivisor π hπ z) A))
  have hcycle (w : C.toScheme) : fiberCycle π hπ w =
      (SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S ▸
        (fiberDivisor π hπ w).weilCycle) := by
    have coe_cast {i j : ℕ} (h : i = j) (c : CycleGroup S.toVariety i) :
        ((cast (congrArg (fun n : ℕ ↦ ↥(CycleGroup S.toVariety n)) h) c :
          CycleGroup S.toVariety j) : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) = c.1 := by
      cases h
      rfl
    have hdim : S.toVariety.dimension - 1 = 1 := by
      rw [show S.toVariety.dimension = 2 from
        (Variety.dim_eq_scheme_dimension S.toVariety).symm.trans S.dim_eq_two]
    have htype : SmoothProjectiveSurface.cycleGroup_dim_sub_one_eq_oneCycle S =
        congrArg (fun n : ℕ ↦ ↥(CycleGroup S.toVariety n)) hdim := Subsingleton.elim _ _
    apply Subtype.ext
    rw [htype]
    exact (coe_cast hdim _).symm
  have eModules : A.lineBundle.toModules ≅ L.toModules := LineBundle.toModulesIso eA
  calc
    L ⬝ fiberCycle π hπ y = A.lineBundle ⬝ fiberCycle π hπ y :=
      (LineBundle.inter_congr eModules _).symm
    _ = surfaceIntersection S A (fiberDivisor π hπ y) := by
      rw [CartierDivisor.lineBundle_inter, hcycle]
      rfl
    _ = surfaceIntersection S A (fiberDivisor π hπ z) := hsymm
    _ = A.lineBundle ⬝ fiberCycle π hπ z := by
      rw [CartierDivisor.lineBundle_inter, hcycle]
      rfl
    _ = L ⬝ fiberCycle π hπ z := LineBundle.inter_congr eModules _

end
