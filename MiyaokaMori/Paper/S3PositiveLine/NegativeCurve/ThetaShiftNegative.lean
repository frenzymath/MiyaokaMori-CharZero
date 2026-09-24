import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberDegree
import MiyaokaMori.Paper.S2WeightedJets.Ygg.FiberDegreePositive
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.RationalTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.ShiftedClassExpansion
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.Targets.HarmonicIntersection
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Negativity of the shifted class

With `θ = d h_k/(2 s_k)` and `H'_k = H_k + θ π_k^*c_1(O_C(p_0))`, one has `(H'_k)^{s_k} = -½ v_k d h_k < 0`
(§2.4 of the paper, proof of Lemma 2.5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private lemma scaled_top_self {K : Type u} [Field K]
    (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Y] (hY : IsProperOver K Y)
    (L : Y.Modules) [L.IsLineBundle] (m s : ℕ) (hs : Y.dimension = s) :
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
        ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle L) s hs =
      (AlgebraicGeometry.topSelfIntersection Y hY L : ℚ) / (m : ℚ) ^ s := by
  have hscale :
      AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
          ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle L) s hs =
        ((m : ℚ)⁻¹) ^ s *
          AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
            (AlgebraicGeometry.ratDivisorOpOfLineBundle L) s hs := by
    unfold AlgebraicGeometry.RatDivisorOp.topSelfIntersection
    rw [AlgebraicGeometry.RatDivisorOp.capPow_smul]
    exact (AlgebraicGeometry.ChowGroupRat.degree Y hY).map_smul _ _
  rw [hscale,
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection_lineBundle Y hY L s hs]
  rw [inv_pow]
  exact inv_mul_eq_div _ _

theorem theta_shift_top_self_intersection_neg {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) (hκ : 1 ≤ κ)
    [AlgebraicGeometry.IsIntegral (YGG f κ)]
    (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme))
    (n : ℕ) (hn : X.toVariety.dim = n) (hn1 : 1 ≤ n) (d : ℤ) (hd : 0 < d)
    (hdeg : TangentBundle.pullbackDegree f = d)
    (hm : 0 < m) (hdiv : (n + 1) * κ * jetWeight κ ∣ m)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (hY : IsProperOver K (YGG f κ)) (hs : (YGG f κ).dimension = (n + 1) * κ)
    (hfib : letI := (YGG.proj f κ).fiberOverSpecResidueField p₀;
      IsProperOver (C.toScheme.residueField p₀) ((YGG.proj f κ).fiber p₀)) :
    let θ : ℚ := (d : ℚ) * harmonic κ / (2 * ((n : ℚ) + 1) * κ)
    let v : ℚ := (AlgebraicGeometry.relativePolarizationFiberDegree (YGG.proj f κ)
      (polarization f κ m) p₀ hfib : ℚ) / (m : ℚ) ^ ((n + 1) * κ - 1)
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection (YGG f κ) hY
        (tautClass f κ m + θ • ratPullbackOp (YGG.proj f κ) (Divisor.ofPoint p₀)) ((n+1)*κ) hs
      = - (v * (d : ℚ) * harmonic κ) / 2
    ∧ AlgebraicGeometry.RatDivisorOp.topSelfIntersection (YGG f κ) hY
        (tautClass f κ m + θ • ratPullbackOp (YGG.proj f κ) (Divisor.ofPoint p₀)) ((n+1)*κ) hs < 0 := by
  dsimp
  have hh := harmonic_intersection f X.embedding (MMSetup.E (f := f)) hn hn1
    (MMSetup.coord (f := f)) (MMSetup.hcoord (f := f)) d hdeg κ hκ m hm hdiv
    p₀ hp₀ hfib hY
  -- `harmonic_intersection` has two further conjuncts after the formula
  -- (explicit fiber degree `v/m^{s-1} = 1/(k!)^{n+1}` and `−d/(k!)^{n+1}·Σ1/q`). They are dropped here
  -- (`-`): keeping them in context makes the later `set v := … / …` try to unify
  -- `↑(relativePolarizationFiberDegree …)` with `1`, which unfolds the intersection number (heartbeat timeout).
  obtain ⟨-, -, -, -, hB, -, hfiberpos, htaut, -, -⟩ := hh
  have hshift := topSelfIntersection_shift f κ m hm p₀ hp₀
    ((d : ℚ) * harmonic κ / (2 * ((n : ℚ) + 1) * κ)) hY ((n + 1) * κ) hs hfib
  have hbase : AlgebraicGeometry.RatDivisorOp.topSelfIntersection (YGG f κ) hY
      (tautClass f κ m) ((n + 1) * κ) hs =
      - ((AlgebraicGeometry.relativePolarizationFiberDegree (YGG.proj f κ)
          (polarization f κ m) p₀ hfib : ℚ) / (m : ℚ) ^ ((n + 1) * κ - 1)) *
        (d : ℚ) * ∑ q ∈ Finset.Icc 1 κ, (1 : ℚ) / (q : ℚ) := by
    calc
      _ = tautologicalTopSelfIntersection (YGG f κ) hY (polarization f κ m) m hm := by
        simpa [tautClass, tautologicalTopSelfIntersection, hs] using
          (scaled_top_self (YGG f κ) hY (polarization f κ m) m ((n + 1) * κ) hs)
      _ = _ := by
        convert htaut using 1 <;>
          simp [YGG, YGG.proj, weightedJetProjection, polarization, jetAlgebra,
            MMSetup.cone, MMSetup.seed, tautologicalTopSelfIntersection, hs] <;>
          rfl
  rw [hshift]
  rw [hbase]
  set v : ℚ :=
    (AlgebraicGeometry.relativePolarizationFiberDegree (YGG.proj f κ)
      (polarization f κ m) p₀ hfib : ℚ) / (m : ℚ) ^ ((n + 1) * κ - 1) with hvdef
  have hv : 0 < v := by
    rw [hvdef]
    apply div_pos
    · exact_mod_cast hfiberpos
    · positivity
  have hnQ : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hκQ : (0 : ℚ) < (κ : ℚ) := by
    exact_mod_cast (show 0 < κ by omega)
  have hdQ : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast hd
  have hhQ : (0 : ℚ) < harmonic κ := harmonic_pos (show κ ≠ 0 by omega)
  have hEq :
      -v * (d : ℚ) * ∑ q ∈ Finset.Icc 1 κ, (1 : ℚ) / (q : ℚ) +
          (((n + 1) * κ : ℕ) : ℚ) *
            ((d : ℚ) * harmonic κ / (2 * ((n : ℚ) + 1) * (κ : ℚ))) * v =
        -(v * (d : ℚ) * harmonic κ) / 2 := by
    rw [harmonic_eq_sum_Icc]
    field_simp [ne_of_gt hnQ, ne_of_gt hκQ]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  constructor
  · exact hEq
  · rw [hEq]
    apply div_neg_of_neg_of_pos
    · exact neg_lt_zero.mpr (mul_pos (mul_pos hv hdQ) hhQ)
    · norm_num

end
