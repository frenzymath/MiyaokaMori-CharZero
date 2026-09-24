import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupVanishesAboveDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator

/-! # The product of two divisor classes pulled back from a curve has degree zero

The product of two divisor classes pulled back from a curve `C`, capped with any 2-dimensional
class, has degree zero: `deg(c_1(π^*L) ∩ c_1(π^*L') ∩ β) = 0` for every `β ∈ CH_2(Y)_ℚ` (`β` need not
be a flat pullback class and `π` need not be flat). The paper says literally that the product
vanishes, and then only takes degrees (proof of Proposition 2.4). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem pullback_divisor_mul_cap_degree_eq_zero {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hY : IsProperOver K Y)
    (hC : IsProperOver K C.carrier)
    (π : Y ⟶ C.carrier) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsProper π]
    (L L' : C.carrier.Modules) [L.IsLineBundle] [L'.IsLineBundle]
    [((AlgebraicGeometry.Scheme.Modules.pullback π).obj L).IsLineBundle]
    [((AlgebraicGeometry.Scheme.Modules.pullback π).obj L').IsLineBundle]
    (β : AlgebraicGeometry.ChowGroupRat Y 2) :
    AlgebraicGeometry.ChowGroupRat.degree Y hY
        (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj L) 0
          (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj L') 1 β)) = 0 := by
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
      ext c
      exact AlgebraicGeometry.chowPushforward_firstChernClass_pullback
        (k := K) π M d c
    change
      ((LinearMap.baseChange ℚ (AlgebraicGeometry.chowPushforward π d).toIntLinearMap).comp
        (LinearMap.baseChange ℚ (AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M)
          (d + 1)).toIntLinearMap)) z =
      ((LinearMap.baseChange ℚ
        (AlgebraicGeometry.firstChernClass M (d + 1)).toIntLinearMap).comp
        (LinearMap.baseChange ℚ
          (AlgebraicGeometry.chowPushforward π (d + 1)).toIntLinearMap)) z
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomp]
  let _ : Subsingleton (AlgebraicGeometry.ChowGroupRat C.carrier 2) :=
    AlgebraicGeometry.ChowGroupRat.subsingleton_of_dimension_lt 2 (by
      rw [C.dim_one]
      norm_num)
  have hpush : AlgebraicGeometry.chowPushforwardRat π 2 β = 0 :=
    Subsingleton.elim _ _
  let γ := AlgebraicGeometry.ratDivisorOpOfLineBundle
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj L) 0
      (AlgebraicGeometry.ratDivisorOpOfLineBundle
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj L') 1 β)
  calc
    AlgebraicGeometry.ChowGroupRat.degree Y hY γ =
        AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
          (AlgebraicGeometry.chowPushforwardRat π 0 γ) :=
      (AlgebraicGeometry.ChowGroupRat.degree_chowPushforwardRat hY hC π γ).symm
    _ = AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
        (AlgebraicGeometry.ratDivisorOpOfLineBundle L 0
          (AlgebraicGeometry.chowPushforwardRat π 1
            (AlgebraicGeometry.ratDivisorOpOfLineBundle
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj L') 1 β))) := by
      rw [hprojection L 0]
    _ = AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
        (AlgebraicGeometry.ratDivisorOpOfLineBundle L 0
          (AlgebraicGeometry.ratDivisorOpOfLineBundle L' 1
            (AlgebraicGeometry.chowPushforwardRat π 2 β))) := by
      rw [hprojection L' 1]
    _ = 0 := by rw [hpush]; simp

end
