import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.Paper.S2WeightedJets.Ygg.VeronesePolarizationVeryAmple
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.CurveInFiberFactors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveToCurveSurjectiveOrConstant
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurveDegreeTensor
import MiyaokaMori.AlgebraicGeometry.Chow.IntegralCurveDegreeTransport
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackVanishesOnFiber
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.RelativelyVeryAmpleFiberAmple
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.ShiftedClassLineBundle
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.YggGeometry
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RestrictionDegreePositiveOfAmple

/-! # Horizontal curves

If an integral closed curve `ι : Γ ↪ Y_k^GG` has `deg(ι^*M) < 0` (`M` a line bundle representing `H'_k`), then `Γ`
is not contained in any fiber (on a fiber the pullback of the fiber class vanishes and the restriction of `B_k` is
ample), so `π_k∘ι` is surjective onto `C` (§2.4 of the paper, proof of Lemma 2.5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem horizontal_of_shifted_degree_neg {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (p₀ : C.toScheme) (a b : ℕ) (hb : 0 < b)
    (Γ : IntegralCurve K (YGG f κ))
    (hneg : Γ.degree (shiftedBundle f κ m p₀ a b) < 0) :
      (¬ ∃ c : C.toScheme, Set.range (Γ.ι ≫ YGG.proj f κ).base ⊆ {c})
      ∧ Function.Surjective (Γ.ι ≫ YGG.proj f κ).base := by
  let g : Γ.carrier ⟶ C.toScheme := Γ.ι ≫ YGG.proj f κ
  have hproper : IsProperOver K Γ.carrier := Γ.isProperOver
  letI : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hdich := range_closedPoint_or_surjective Γ.carrier hproper g
  have hclosedContra (c : C.toScheme)
      (hc : IsClosed ({c} : Set C.toScheme))
      (hr : Set.range g.base ⊆ {c}) : False := by
    obtain ⟨j, hjclosed, hj⟩ :=
      AlgebraicGeometry.exists_closedImmersion_to_fiber_of_range_subset
        Γ.ι (YGG.proj f κ) c hc hr
    letI : AlgebraicGeometry.IsClosedImmersion j := hjclosed
    letI : ((YGG.proj f κ).fiber c).Over
        (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      ⟨(YGG.proj f κ).fiberι c ≫
        YGG.proj f κ ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
    letI : AlgebraicGeometry.IsProper
        (j ≫ ((YGG.proj f κ).fiber c ↘
          AlgebraicGeometry.Spec (CommRingCat.of K))) := by
      change AlgebraicGeometry.IsProper
        (j ≫ (YGG.proj f κ).fiberι c ≫
          YGG.proj f κ ≫
          (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
      rw [← Category.assoc, hj]
      exact Γ.isProper
    let Γf : IntegralCurve K ((YGG.proj f κ).fiber c) :=
      { carrier := Γ.carrier
        ι := j
        dim_eq_one := Γ.dim_eq_one }
    have hzero := degree_pullback_eq_zero_of_in_fiber
      (YGG.proj f κ)
      (Divisor.ofPoint p₀).lineBundle.toModules Γ c hc hr
    have hpos : 0 < Γf.degree
        ((AlgebraicGeometry.Scheme.Modules.pullback
          ((YGG.proj f κ).fiberι c)).obj (polarization f κ m)) := by
      have hvery : AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple
          (YGG.proj f κ) (polarization f κ m) := by
        change AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple
          (AlgebraicGeometry.Scheme.relativeProj (jetAlgebra f κ)).hom
          (AlgebraicGeometry.Scheme.relativeProj.twist (jetAlgebra f κ) (m : ℤ))
        have hmpos : 0 < m :=
          (Fact.out : (jetAlgebra f κ).SufficientlyDivisible m).1
        have hgen : ((jetAlgebra f κ).veronese m).GeneratedInDegreeOne :=
          (Fact.out : (jetAlgebra f κ).SufficientlyDivisible m).2
        let e := AlgebraicGeometry.Scheme.relativeProj.veroneseIso
          (jetAlgebra f κ) m hmpos
        have hi : AlgebraicGeometry.IsClosedImmersion e.inv.left := by
          have hleft : e.inv.left ≫ e.hom.left = 𝟙 _ := by
            exact congrArg CategoryTheory.Over.Hom.left e.inv_hom_id
          have hcomp : AlgebraicGeometry.IsClosedImmersion
              (e.inv.left ≫ e.hom.left) := by
            rw [hleft]
            infer_instance
          exact AlgebraicGeometry.IsClosedImmersion.of_comp e.inv.left e.hom.left
        have hover : e.inv.left ≫
            (AlgebraicGeometry.Scheme.relativeProj
              ((jetAlgebra f κ).veronese m)).hom =
            (AlgebraicGeometry.Scheme.relativeProj (jetAlgebra f κ)).hom := by
          exact CategoryTheory.Over.w e.inv
        refine ⟨(jetAlgebra f κ).veronese m, e.inv.left, hgen, hi, hover, ?_⟩
        exact AlgebraicGeometry.Scheme.relativeProj.veronese_twist_pullback_iso
          (jetAlgebra f κ) m hmpos
      haveI : AlgebraicGeometry.IsProper (YGG.proj f κ) := YGG.proj_isProper f rfl κ
      exact degree_restrict_pos_of_ample
        (AlgebraicGeometry.isAmple_fiber_of_isRelativelyVeryAmple_of_quasiCompact
          (YGG.proj f κ) (polarization f κ m) hvery c) Γf
    have htransport := IntegralCurve.degree_factor Γ
      ((YGG.proj f κ).fiberι c) j hj
      (by
        change AlgebraicGeometry.IsProper
          (j ≫ (YGG.proj f κ).fiberι c ≫
            YGG.proj f κ ≫
            (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
        rw [← Category.assoc, hj]
        exact Γ.isProper)
      (polarization f κ m)
    have hdegpol : 0 < Γ.degree (polarization f κ m) := by
      rw [htransport]
      exact hpos
    have hdegshift := IntegralCurve.degree_tensor Γ
      (AlgebraicGeometry.Scheme.Modules.tensorPow (polarization f κ m) b)
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
          (Divisor.ofPoint p₀).lineBundle.toModules) (m * a))
    have hpowP := IntegralCurve.degree_tensorPow Γ (polarization f κ m) b
    have hpowQ := IntegralCurve.degree_tensorPow Γ
      ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
        (Divisor.ofPoint p₀).lineBundle.toModules) (m * a)
    have hshift : Γ.degree (shiftedBundle f κ m p₀ a b) =
        (b : ℤ) * Γ.degree (polarization f κ m) := by
      change Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow (polarization f κ m) b)
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
            (Divisor.ofPoint p₀).lineBundle.toModules) (m * a))) = _
      rw [hdegshift, hpowP, hpowQ, hzero]
      push_cast
      ring
    rw [hshift] at hneg
    have hbz : (0 : ℤ) < b := by exact_mod_cast hb
    nlinarith
  rcases hdich with ⟨c, hc, hr⟩ | hs
  · exact (hclosedContra c hc hr).elim
  · refine ⟨?_, hs⟩
    rintro ⟨c, hr⟩
    have hsub : Subsingleton C.toScheme := by
      constructor
      intro x y
      have hx := hr (hs x)
      have hy := hr (hs y)
      have hxc : x = c := Set.mem_singleton_iff.mp hx
      have hyc : y = c := Set.mem_singleton_iff.mp hy
      exact hxc.trans hyc.symm
    letI : Subsingleton C.toScheme := hsub
    letI : DiscreteTopology C.toScheme := by infer_instance
    have hle : topologicalKrullDim C.toScheme ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology C.toScheme
    rw [C.dim_one] at hle
    norm_num at hle

end
