import MiyaokaMori.Paper.S2WeightedJets.Intersection.PushforwardTautologicalPower
import MiyaokaMori.AlgebraicGeometry.Chow.CurveDegreeEqTopSelfIntersection
import MiyaokaMori.Paper.S2WeightedJets.Intersection.PullbackClassDegreeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.RationalTopSelfIntersection

/-! # Degree of a pulled-back class against the tautological power

The projection formula gives `deg(π_sp^*c_1(Q_i) ∩ H^{s_k−1} ∩ [Y^sp]) = v · deg Q_i`, where
`v = (fiber degree at a closed point c)/m^{s_k−1}` (proof of Proposition 2.4 of the paper,
eq. (2.9)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem degree_taut_pow_cap_pullback {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ} (hkk : 1 ≤ kk) {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m)
    [AlgebraicGeometry.IsIntegral (splitWeightedProjectivization F kk).left]
    [AlgebraicGeometry.IsProper (splitWeightedProjectivization F kk).hom]
    [SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ))]
    (hdim : (splitWeightedProjectivization F kk).left.dimension = (n + 1) * kk)
    (hY : letI : (splitWeightedProjectivization F kk).left.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
        ⟨(splitWeightedProjectivization F kk).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩;
      IsProperOver K (splitWeightedProjectivization F kk).left)
    (i : Fin (n + 1)) (c : C.carrier) (hc : IsClosed {c})
    (h₁ : letI := (splitWeightedProjectivization F kk).hom.fiberOverSpecResidueField c;
      IsProperOver (C.carrier.residueField c) ((splitWeightedProjectivization F kk).hom.fiber c)) :
    letI : (splitWeightedProjectivization F kk).left.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      ⟨(splitWeightedProjectivization F kk).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩;
    AlgebraicGeometry.ChowGroupRat.degree (splitWeightedProjectivization F kk).left hY
        (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (splitWeightedProjectivization F kk).hom).obj (F.lineQuotient i).toModules) 0
          (AlgebraicGeometry.RatDivisorOp.capPow
            (ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm))
            ((n + 1) * kk - 1) 1
            (AlgebraicGeometry.ChowGroupRat.congr (splitWeightedProjectivization F kk).left
              (weighted_dimension_eq_succ_sub_one hkk)
              (AlgebraicGeometry.fundamentalClassRat
                (splitWeightedProjectivization F kk).left ((n + 1) * kk) hdim))))
      = ((AlgebraicGeometry.relativePolarizationFiberDegree (splitWeightedProjectivization F kk).hom
            (AlgebraicGeometry.Scheme.relativeProj.twist
              (splitWeightedAlgebraOf F kk) (m : ℤ)) c h₁ : ℚ)
          / (m : ℚ) ^ ((n + 1) * kk - 1)) * (LineBundle.degree (F.lineQuotient i) : ℚ) := by
  let Y := (splitWeightedProjectivization F kk).left
  let π := (splitWeightedProjectivization F kk).hom
  let _ : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨π ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  let _ : π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  let β := AlgebraicGeometry.RatDivisorOp.capPow
    (ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm))
    ((n + 1) * kk - 1) 1
    (AlgebraicGeometry.ChowGroupRat.congr Y
      (by
        have : 1 ≤ (n + 1) * kk :=
          Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (Nat.succ_ne_zero n) (by omega))
        omega : (n + 1) * kk = 1 + ((n + 1) * kk - 1))
      (AlgebraicGeometry.fundamentalClassRat Y ((n + 1) * kk) hdim))
  have hC : IsProperOver K C.carrier :=
    ((isProjectiveOver_iff_isProper_and_isAmple K C.carrier).mp C.projective).1
  have hprojection (M : C.carrier.Modules) [M.IsLineBundle]
      [((AlgebraicGeometry.Scheme.Modules.pullback π).obj M).IsLineBundle]
      (d : ℕ) (z : AlgebraicGeometry.ChowGroupRat Y (d + 1)) :
      AlgebraicGeometry.chowPushforwardRat π d
          (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M) d z) =
        AlgebraicGeometry.ratDivisorOpOfLineBundle M d
          (AlgebraicGeometry.chowPushforwardRat π (d + 1) z) := by
    have hcomp :
        (AlgebraicGeometry.chowPushforward π d).toIntLinearMap ∘ₗ
            (AlgebraicGeometry.firstChernClass
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M)
              (d + 1)).toIntLinearMap =
          (AlgebraicGeometry.firstChernClass M (d + 1)).toIntLinearMap ∘ₗ
            (AlgebraicGeometry.chowPushforward π (d + 1)).toIntLinearMap := by
      ext z
      exact AlgebraicGeometry.chowPushforward_firstChernClass_pullback
        (k := K) π M d z
    change
      ((LinearMap.baseChange ℚ
          (AlgebraicGeometry.chowPushforward π d).toIntLinearMap).comp
        (LinearMap.baseChange ℚ (AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M)
          (d + 1)).toIntLinearMap)) z =
      ((LinearMap.baseChange ℚ
          (AlgebraicGeometry.firstChernClass M (d + 1)).toIntLinearMap).comp
        (LinearMap.baseChange ℚ
          (AlgebraicGeometry.chowPushforward π (d + 1)).toIntLinearMap)) z
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomp]
  have hdimC : C.carrier.dimension = 1 := by
    unfold AlgebraicGeometry.Scheme.dimension
    rw [C.dim_one]
    simp
  have hcurve :
      AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
          (AlgebraicGeometry.ratDivisorOpOfLineBundle
            (F.lineQuotient i).toModules 0
            (AlgebraicGeometry.fundamentalClassRat C.carrier 1 hdimC)) =
        (LineBundle.degree (F.lineQuotient i) : ℚ) := by
    have htop := AlgebraicGeometry.RatDivisorOp.topSelfIntersection_lineBundle
      C.carrier hC (F.lineQuotient i).toModules 1 hdimC
    calc
      _ = (AlgebraicGeometry.topSelfIntersection C.carrier hC
          (F.lineQuotient i).toModules : ℚ) := by
        simpa [AlgebraicGeometry.RatDivisorOp.topSelfIntersection,
          AlgebraicGeometry.RatDivisorOp.capPow] using htop
      _ = (LineBundle.degree (F.lineQuotient i) : ℚ) := by
        rw [LineBundle.degree_eq_topSelfIntersection C hC (F.lineQuotient i)]
  calc
    AlgebraicGeometry.ChowGroupRat.degree Y hY
        (AlgebraicGeometry.ratDivisorOpOfLineBundle
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
            (F.lineQuotient i).toModules) 0 β) =
      AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
        (AlgebraicGeometry.chowPushforwardRat π 0
          (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
              (F.lineQuotient i).toModules) 0 β)) :=
      (AlgebraicGeometry.ChowGroupRat.degree_chowPushforwardRat
        hY hC π _).symm
    _ = AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
        (AlgebraicGeometry.ratDivisorOpOfLineBundle
          (F.lineQuotient i).toModules 0
          (AlgebraicGeometry.chowPushforwardRat π 1 β)) := by
      rw [hprojection]
    _ = AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
        (AlgebraicGeometry.ratDivisorOpOfLineBundle
          (F.lineQuotient i).toModules 0
          (((AlgebraicGeometry.relativePolarizationFiberDegree π
                (AlgebraicGeometry.Scheme.relativeProj.twist
                  (splitWeightedAlgebraOf F kk) (m : ℤ)) c h₁ : ℚ)
              / (m : ℚ) ^ ((n + 1) * kk - 1)) •
            AlgebraicGeometry.fundamentalClassRat C.carrier 1 hdimC)) := by
      rw [pushforward_taut_pow_eq_fiberDegree hkk F m hm hdiv hdim c hc h₁]
    _ = ((AlgebraicGeometry.relativePolarizationFiberDegree π
              (AlgebraicGeometry.Scheme.relativeProj.twist
                (splitWeightedAlgebraOf F kk) (m : ℤ)) c h₁ : ℚ)
            / (m : ℚ) ^ ((n + 1) * kk - 1)) *
          (LineBundle.degree (F.lineQuotient i) : ℚ) := by
      rw [map_smul, map_smul, hcurve]
      simp only [smul_eq_mul]

end
