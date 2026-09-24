import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Divisors.OrdNonnegOfRegularX
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveStalkDVR
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrder
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveDivisor

/-! # Weighted order bound for monomials

A monomial of weight `q` (with coefficient regular at `z`) vanishes to order `≥ q·β_z`
(§3 of the paper: "every monomial in a transformed coordinate of weight `q` has order at least `qβ_z`").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open MiyaokaMori.WeightedJets in
/-- At a point of coheight `1`: the specialization of `weightedPolynomial_order_lowerBound` to the monomial `c · X^d`. -/
theorem ord_monomial_ge_weight_mul_beta_of_coheight_one {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} {n κ q : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0)
    (z : Ct.toScheme) (hco : Order.coheight z = 1)
    {U : Ct.toScheme.Opens} [Nonempty U] (hzU : z ∈ U)
    (c : Γ(Ct.toScheme, U)) (d : Fin (n + 1) × Fin κ →₀ ℕ)
    (hw : ∑ p ∈ d.support, d p * ((p.2 : ℕ) + 1) = q) (hq : 0 < q)
    (hprod : (Ct.toScheme.germToFunctionField U c) * ∏ p ∈ d.support, (a p.1 p.2) ^ d p ≠ 0) :
    (q : ℚ) * weightedOrderQ a hne z ≤
      (Ct.toScheme.ord ((Ct.toScheme.germToFunctionField U c) *
        ∏ p ∈ d.support, (a p.1 p.2) ^ d p) z : ℚ) := by
  have : IsDiscreteValuationRing (Ct.toScheme.presheaf.stalk z) :=
    Ct.isDiscreteValuationRing_stalk z hco
  set v := AlgebraicGeometry.Divisors.CurveStalkValuation.valuation Ct.toScheme z hco with hv
  set c' := Ct.toScheme.germToFunctionField U c with hc'
  let a' : JetCoordinate n κ → Ct.toScheme.functionField := fun p ↦ a p.1 p.2
  have hhom : (MvPolynomial.monomial d c').IsWeightedHomogeneous
      (fun p : JetCoordinate n κ ↦ (jetCoordinateWeight p : ℕ)) ((⟨q, hq⟩ : ℕ+) : ℕ) := by
    apply MvPolynomial.isWeightedHomogeneous_monomial
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    exact hw  -- `(jetCoordinateWeight p : ℕ) = p.2 + 1` holds by definition
  have hreg : ∀ e, 0 ≤ v ((MvPolynomial.monomial d c').coeff e) := by
    intro e
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_germToFunctionField_nonneg _ z hco hzU c
    · simp
  have hbound : ∀ p, ((weightedOrderQ a hne z : ℚ) : WithTop ℚ) ≤
      normalizedOrder v (jetCoordinateWeight p) (a' p) := by
    intro p
    rw [coe_weightedOrder]
    -- `weightedOrderTop a z` is `weightedOrder` specialized to the order function `ordTop · z`; at a coheight-1 DVR
    -- point this order function is the stalk valuation `v` (`ordTop_fun_eq_valuation`).
    show weightedOrder jetCoordinateWeight (fun f ↦ Ct.toScheme.ordTop f z) a' ≤ _
    rw [Ct.toScheme.ordTop_fun_eq_valuation z hco]
    exact weightedOrder_le_coordinate jetCoordinateWeight v a' p
  have key := weightedPolynomial_order_lowerBound jetCoordinateWeight v (MvPolynomial.monomial d c')
    ⟨q, hq⟩ hhom hreg a' _ hbound
  rw [MvPolynomial.eval_monomial, Finsupp.prod] at key
  have e : normalizedOrder v (⟨q, hq⟩ : ℕ+) (c' * ∏ p ∈ d.support, a' p ^ d p) =
      (((Ct.toScheme.ord (c' * ∏ p ∈ d.support, a p.1 p.2 ^ d p) z : ℤ) : ℚ) /
        (((⟨q, hq⟩ : ℕ+) : ℕ) : ℚ) : ℚ) :=
    normalizedOrder_of_eq v _ _ _
      (AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_of_ne_zero _ z hco hprod)
  have key' := WithTop.coe_le_coe.mp (key.trans_eq e)
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have := (le_div_iff₀ (by simpa using hq')).mp key'
  simpa [mul_comm] using this

theorem ord_monomial_ge_weight_mul_beta {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} {n κ q : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0)
    (z : Ct.toScheme) {U : Ct.toScheme.Opens} [Nonempty U] (hzU : z ∈ U)
    (c : Γ(Ct.toScheme, U)) (hc : c ≠ 0) (d : Fin (n + 1) × Fin κ →₀ ℕ)
    (hw : ∑ p ∈ d.support, d p * ((p.2 : ℕ) + 1) = q) (hq : 0 < q)
    (hprod : (Ct.toScheme.germToFunctionField U c) * ∏ p ∈ d.support, (a p.1 p.2) ^ d p ≠ 0) :
    (q : ℚ) * weightedOrderQ a hne z ≤
      (Ct.toScheme.ord ((Ct.toScheme.germToFunctionField U c) *
        ∏ p ∈ d.support, (a p.1 p.2) ^ d p) z : ℚ) := by
  by_cases hco : Order.coheight z = 1
  · exact ord_monomial_ge_weight_mul_beta_of_coheight_one a hne z hco hzU c d hw hq hprod
  · -- a point not of codimension one: all orders are 0, so β_z ≤ 0 and the right-hand side is 0
    obtain ⟨i, q₀, hiq⟩ := hne
    have hβ := weightedOrder_le a ⟨i, q₀, hiq⟩ z i q₀ hiq
    rw [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hco] at hβ
    rw [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hco]
    have hq' : (0 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq.le
    simp only [Int.cast_zero, zero_div] at hβ ⊢
    exact mul_nonpos_of_nonneg_of_nonpos hq' hβ

end
