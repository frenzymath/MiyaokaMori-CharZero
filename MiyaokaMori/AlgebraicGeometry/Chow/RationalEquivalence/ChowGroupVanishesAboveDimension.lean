import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite

/-! # The Chow group vanishes above the dimension

For `k > dim X` one has `CH_k(X)_ℚ = 0`: `X` has no point of dimension `k`, so `Z_k(X) = 0`
(for example `CH_2(C)_ℚ = 0` on a curve `C`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.ChowGroupRat.subsingleton_of_dimension_lt
    {X : AlgebraicGeometry.Scheme.{u}} (k : ℕ) (hk : topologicalKrullDim X < (k : WithBot ℕ∞)) :
    Subsingleton (AlgebraicGeometry.ChowGroupRat X k) := by
  have hzero : ∀ c : ↥(AlgebraicGeometry.cycleSubgroup X k),
      (c : AlgebraicGeometry.AlgebraicCycle X ℤ) = 0 := by
    intro c
    ext x
    by_contra hcx
    have hdim : Order.height x = (k : ℕ∞) := c.2 x hcx
    have hheight : (Order.height x : WithBot ℕ∞) ≤ Order.krullDim X :=
      Order.height_le_krullDim x
    rw [AlgebraicGeometry.krullDim_eq_topologicalKrullDim X] at hheight
    have hcast : (Order.height x : WithBot ℕ∞) = (k : WithBot ℕ∞) := by
      exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) hdim
    rw [hcast] at hheight
    exact (not_lt_of_ge hheight) hk
  have hchow : Subsingleton (AlgebraicGeometry.ChowGroup X k) := by
    constructor
    intro a b
    induction a using QuotientAddGroup.induction_on with
    | _ a =>
      induction b using QuotientAddGroup.induction_on with
      | _ b =>
        rw [show a = 0 from Subtype.ext (hzero a)]
        rw [show b = 0 from Subtype.ext (hzero b)]
  constructor
  intro a b
  have hzeroRat : ∀ z : AlgebraicGeometry.ChowGroupRat X k, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y =>
      rw [show y = 0 from Subsingleton.elim y 0, TensorProduct.tmul_zero]
      rfl
    | add x y hx hy =>
      calc
        x + y = 0 + 0 := congrArg₂ (· + ·) hx hy
        _ = 0 := add_zero 0
  exact (hzeroRat a).trans (hzeroRat b).symm

end
