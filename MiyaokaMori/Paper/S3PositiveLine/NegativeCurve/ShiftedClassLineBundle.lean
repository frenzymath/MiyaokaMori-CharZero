import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalClass
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.YggProjLocallyOfFiniteType
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor

/-! # A line bundle representing the shifted class

Clearing denominators, `H'_k` is the `c_1` of a line bundle: for `θ = a/b` (`a, b ∈ ℕ`, `b > 0`),
`(m·b)•(H_k + θ π_k^*c_1(O_C(p_0))) = c_1(B_k^{⊗b} ⊗ π_k^*O_C(p_0)^{⊗ma})`. This is the `ℚ`-Cartier datum
implicit in the paper's use of a rational Cartier class in the proof of Lemma 2.5 (§2.4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The line bundle `M = B_k^{⊗b} ⊗ π_k^*O_C(p₀)^{⊗(m·a)}` representing `H'_k`. -/

noncomputable def shiftedBundle {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) (p₀ : C.toScheme) (a b : ℕ) :
    (YGG f κ).Modules :=
  AlgebraicGeometry.Scheme.Modules.tensor
    (AlgebraicGeometry.Scheme.Modules.tensorPow (polarization f κ m) b)
    (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
        (Divisor.ofPoint p₀).lineBundle.toModules) (m * a))

instance shiftedBundle_isLineBundle {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (p₀ : C.toScheme) (a b : ℕ) : (shiftedBundle f κ m p₀ a b).IsLineBundle := by
  change (AlgebraicGeometry.Scheme.Modules.tensor
    (AlgebraicGeometry.Scheme.Modules.tensorPow (polarization f κ m) b)
    (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
        (Divisor.ofPoint p₀).lineBundle.toModules) (m * a))).IsLineBundle
  infer_instance

private lemma ratDivisorOp_tensor {K : Type u} [Field K]
    {Y : AlgebraicGeometry.Scheme} [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))]
    (L M : Y.Modules) [L.IsLineBundle] [M.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.tensor L M).IsLineBundle] :
    AlgebraicGeometry.ratDivisorOpOfLineBundle
        (AlgebraicGeometry.Scheme.Modules.tensor L M) =
      AlgebraicGeometry.ratDivisorOpOfLineBundle L +
        AlgebraicGeometry.ratDivisorOpOfLineBundle M := by
  funext d
  ext α
  change (AlgebraicGeometry.firstChernClass
      (AlgebraicGeometry.Scheme.Modules.tensor L M) (d + 1)).ratExtend α =
    (AlgebraicGeometry.firstChernClass L (d + 1)).ratExtend α +
      (AlgebraicGeometry.firstChernClass M (d + 1)).ratExtend α
  rw [AlgebraicGeometry.firstChernClass_tensor (k := K)]
  change (LinearMap.baseChange ℚ
      ((AlgebraicGeometry.firstChernClass L (d + 1)).toIntLinearMap +
        (AlgebraicGeometry.firstChernClass M (d + 1)).toIntLinearMap)) α = _
  rw [LinearMap.baseChange_add]
  rfl

private lemma ratDivisorOp_tensorPow {K : Type u} [Field K]
    {Y : AlgebraicGeometry.Scheme} [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))]
    (L : Y.Modules) [L.IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.ratDivisorOpOfLineBundle
        (AlgebraicGeometry.Scheme.Modules.tensorPow L q) =
      (q : ℚ) • AlgebraicGeometry.ratDivisorOpOfLineBundle L := by
  induction q with
  | zero =>
      funext d
      ext α
      change (AlgebraicGeometry.firstChernClass
          (SheafOfModules.unit Y.ringCatSheaf) (d + 1)).ratExtend α = _
      rw [AlgebraicGeometry.firstChernClass_one]
      unfold AddMonoidHom.ratExtend
      have hz :
          (AddMonoidHom.toIntLinearMap
              (0 : AlgebraicGeometry.ChowGroup Y (d + 1) →+
                AlgebraicGeometry.ChowGroup Y d)) =
            (0 : AlgebraicGeometry.ChowGroup Y (d + 1) →ₗ[ℤ]
              AlgebraicGeometry.ChowGroup Y d) := by
        ext x
        rfl
      rw [hz, LinearMap.baseChange_zero]
      rw [Nat.cast_zero, zero_smul]
      rfl
  | succ q ih =>
      change AlgebraicGeometry.ratDivisorOpOfLineBundle
          (AlgebraicGeometry.Scheme.Modules.tensor
            (AlgebraicGeometry.Scheme.Modules.tensorPow L q) L) =
        ((q + 1 : ℕ) : ℚ) • AlgebraicGeometry.ratDivisorOpOfLineBundle L
      rw [ratDivisorOp_tensor (K := K) (Y := Y), ih]
      simp [add_smul]

theorem shiftedBundle_ratDivisorOp {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) (hm : 0 < m)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (p₀ : C.toScheme) (a b : ℕ) (hb : 0 < b) :
    ((m * b : ℕ) : ℚ) • (tautClass f κ m
        + ((a : ℚ) / (b : ℚ)) • ratPullbackOp (YGG.proj f κ) (Divisor.ofPoint p₀))
      = AlgebraicGeometry.ratDivisorOpOfLineBundle (shiftedBundle f κ m p₀ a b) := by
  letI : AlgebraicGeometry.LocallyOfFiniteType (YGG.proj f κ) :=
    YGG.proj_locallyOfFiniteType_inst f κ
  letI : AlgebraicGeometry.LocallyOfFiniteType
      (YGG.proj f κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
    infer_instance
  letI : AlgebraicGeometry.LocallyOfFiniteType
      (YGG f κ ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    change AlgebraicGeometry.LocallyOfFiniteType
      (YGG.proj f κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  let L := polarization f κ m
  let M := (AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
    (Divisor.ofPoint p₀).lineBundle.toModules
  have hmQ : (m : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hbQ : (b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb)
  have hpowL := ratDivisorOp_tensorPow (K := K) (Y := YGG f κ) L b
  have hpowM := ratDivisorOp_tensorPow (K := K) (Y := YGG f κ) M (m * a)
  have htensor := ratDivisorOp_tensor (K := K) (Y := YGG f κ)
    (AlgebraicGeometry.Scheme.Modules.tensorPow L b)
    (AlgebraicGeometry.Scheme.Modules.tensorPow M (m * a))
  change ((m * b : ℕ) : ℚ) •
      ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle L +
        ((a : ℚ) / (b : ℚ)) • AlgebraicGeometry.ratDivisorOpOfLineBundle M) =
    AlgebraicGeometry.ratDivisorOpOfLineBundle
      (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow L b)
        (AlgebraicGeometry.Scheme.Modules.tensorPow M (m * a)))
  rw [htensor, hpowL, hpowM]
  rw [smul_add, smul_smul, smul_smul]
  have hmb : ((m * b : ℕ) : ℚ) * (m : ℚ)⁻¹ = (b : ℚ) := by
    rw [Nat.cast_mul]
    field_simp
  have hma : ((m * b : ℕ) : ℚ) * ((a : ℚ) / (b : ℚ)) = ((m * a : ℕ) : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    field_simp
  rw [hmb, hma]

end
