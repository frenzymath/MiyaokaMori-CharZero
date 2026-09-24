import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetTransition
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetTransitionRelated
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.MonomialWeightedOrderBound
import MiyaokaMori.RingTheory.OrderOfVanishing.NormalDimensionOneDvr
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrder
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveStalkDVR

/-! # Chart independence of the weighted order

`β_z` does not depend on the jet chart: after a change of chart every monomial of weight `q` has order `≥ qβ_z`,
so the minimum cannot decrease; applying this to the inverse transition gives the reverse inequality
(§3 of the paper: "a change of chart cannot decrease the minimum … reverse inequality").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open MiyaokaMori.WeightedJets MvPolynomial

/-- Public restatement of the private lemma `weightedOrder_le_eval_weightedPolynomial` of `WeightedJetValuation`
(proved from the public `weightedPolynomial_order_lowerBound`): a weight-preserving polynomial substitution with
regular coefficients does not decrease the weighted order. `weightedOrder_invariant` requires a
`WeightedPolynomialEquiv` that is invertible at the level of polynomials, while `JetTransitionRelated` only gives one
step in each direction, so we use the one-sided inequality twice and antisymmetry. -/
theorem MiyaokaMori.WeightedJets.weightedOrder_le_eval {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (w : ι → ℕ+) (v : AddValuation K (WithTop ℤ)) (p : ι → MvPolynomial ι K)
    (hp : ∀ i, (p i).IsWeightedHomogeneous (fun j ↦ (w j : ℕ)) (w i : ℕ))
    (hreg : ∀ i d, 0 ≤ v ((p i).coeff d)) (a : ι → K) :
    MiyaokaMori.WeightedJets.weightedOrder w v a ≤
      MiyaokaMori.WeightedJets.weightedOrder w v (fun i ↦ eval a (p i)) := by
  apply WithTop.forall_coe_le_iff_le.mp
  intro β hβ
  apply Finset.le_inf
  intro i _
  exact weightedPolynomial_order_lowerBound w v (p i) (w i) (hp i) (hreg i) a β
    (fun j ↦ hβ.trans (weightedOrder_le_coordinate w v a j))

/-- One jet transition step (with coefficients regular at `z`) does not decrease the weighted order. Only the
coefficients `g p.2 p.1 j` of weight `p.2` need to be regular at `z`. -/
theorem weightedOrderTop_le_of_jetTransitionStep {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} {n κ : ℕ}
    (a a' : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (z : Ct.toScheme) (hco : Order.coheight z = 1) (h : JetTransitionStep a a' z) :
    weightedOrderTop a z ≤ weightedOrderTop a' z := by
  have : IsDiscreteValuationRing (Ct.toScheme.presheaf.stalk z) :=
    Ct.isDiscreteValuationRing_stalk z hco
  obtain ⟨g, P, -, hP, heq⟩ := h
  let φ := algebraMap (Ct.toScheme.presheaf.stalk z) Ct.toScheme.functionField
  let FR : JetCoordinate n κ → MvPolynomial (JetCoordinate n κ) (Ct.toScheme.presheaf.stalk z) :=
    fun p ↦ (∑ j, C (g p.2 p.1 j) * X (j, p.2)) + P p.1 p.2
  have hFR : ∀ p, (FR p).IsWeightedHomogeneous (fun j ↦ (jetCoordinateWeight j : ℕ))
      (jetCoordinateWeight p : ℕ) := by
    intro p
    refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.sum _ _ _ fun j _ ↦ ?_)
      (hP p.1 p.2).weighted_homogeneous
    exact (isWeightedHomogeneous_X _ (fun j ↦ (jetCoordinateWeight j : ℕ)) (j, p.2)).C_mul _
  have hfun : (fun p : JetCoordinate n κ ↦ a' p.1 p.2) =
      fun p ↦ eval (fun p : JetCoordinate n κ ↦ a p.1 p.2) (map φ (FR p)) := by
    funext p
    rw [heq p.1 p.2, eval_map, aeval_def]
    simp only [FR, eval₂_add, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X]
    rfl
  -- `weightedOrderTop` is `weightedOrder` specialized to the order function `ordTop · z`; at a coheight-1 DVR point
  -- this order function is the stalk valuation (`ordTop_fun_eq_valuation`), so the `AddValuation` inequalities apply.
  show weightedOrder jetCoordinateWeight (fun f ↦ Ct.toScheme.ordTop f z) (fun p ↦ a p.1 p.2) ≤
    weightedOrder jetCoordinateWeight (fun f ↦ Ct.toScheme.ordTop f z) (fun p ↦ a' p.1 p.2)
  rw [Ct.toScheme.ordTop_fun_eq_valuation z hco, hfun]
  refine MiyaokaMori.WeightedJets.weightedOrder_le_eval jetCoordinateWeight _ (fun p ↦ map φ (FR p)) ?_ ?_ _
  · intro p d hd
    rw [coeff_map] at hd
    exact hFR p (fun h0 ↦ hd (by rw [h0, map_zero]))
  · intro p d
    rw [coeff_map]
    exact AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_algebraMap_nonneg _ z hco _

theorem weightedOrder_chart_independent {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} {n κ : ℕ}
    (a a' : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0) (hne' : ∃ i q, a' i q ≠ 0)
    (z : Ct.toScheme) (hz : IsClosed ({z} : Set Ct.toScheme))
    (htrans : JetTransitionRelated a a' z) :
    weightedOrderQ a hne z = weightedOrderQ a' hne' z := by
  have hco := Ct.coheight_eq_one_of_isClosed z hz
  apply WithTop.coe_injective
  rw [coe_weightedOrder, coe_weightedOrder]
  exact le_antisymm (weightedOrderTop_le_of_jetTransitionStep a a' z hco htrans.1)
    (weightedOrderTop_le_of_jetTransitionStep a' a z hco htrans.2)

end
