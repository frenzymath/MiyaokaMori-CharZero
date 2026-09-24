import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Integer powers and the scheme's order of vanishing

For a nonzero rational function on an integral locally Noetherian scheme, the
existing `Scheme.ord` multiplies by an integer exponent. Negative and zero
exponents are included. At points whose coheight is not one, the formula uses
the original order's junk value zero on both sides.

This is the arithmetic for the signed local equations of the divisor `D_L` in the proof of
Lemma 3.1 of the paper. It does not construct a Cartier divisor or a line bundle, and
it does not assume that the local rings are DVRs. Sources: Stacks Project,
Divisors, Definition `definition-order-vanishing` and its product formula;
Algebra, Definition `definition-ord` and Lemma `lemma-ord-additive`.
-/

namespace AlgebraicGeometry.Divisors.FunctionFieldOrderPowers

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The order of a nonzero rational function raised to an integer power scales by that integer. -/
theorem ord_zpow {f : X.functionField} (hf : f ≠ 0) (m : ℤ) (x : X) :
    Scheme.ord (f ^ m) x = m * Scheme.ord f x := by
  by_cases hx : coheight x = 1
  · rw [Scheme.ord_eq_unzero_ordHom hx (zpow_ne_zero m hf),
      WithZero.toAdd_unzero_eq_log, map_zpow₀, WithZero.log_zpow,
      Scheme.ord_eq_unzero_ordHom hx hf, WithZero.toAdd_unzero_eq_log, Int.zsmul_eq_mul]
  · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hx, mul_zero]

end AlgebraicGeometry.Divisors.FunctionFieldOrderPowers
