import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.FunctionFieldOrderPowers

/-! # Order of vanishing of a power

If a rational function `b` is the `m`-th power of a nonzero rational function `c`, then
`ord_y b = m · ord_y c`; in particular `(m : ℤ) ∣ ord_y b`.

This is the integrality statement `ord_y(b_{α,i,q}) / q ∈ ℤ` used in the proof of
Lemma 3.1 of the paper.

Proof: `Scheme.ord` is a discrete valuation on nonzero rational functions at points of coheight
one and takes the value `0` elsewhere; in both cases `ord (c ^ m) = m · ord c`. The integer-power
version is `AlgebraicGeometry.Divisors.FunctionFieldOrderPowers.ord_zpow`; the natural-number power is the special
case obtained through `zpow_natCast`.

The hypothesis `c ≠ 0` cannot be dropped in the form used by `ord_zpow`: `ord 0` is `0` by
convention while `0 ^ 0 = 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- Order of a power: `b = c ^ m` with `c ≠ 0` implies `ord_x b = m · ord_x c`.
Specialization of `AlgebraicGeometry.Divisors.FunctionFieldOrderPowers.ord_zpow`. -/
theorem ord_eq_mul_of_eq_pow {b c : X.functionField} (hc : c ≠ 0) {m : ℕ} (hb : b = c ^ m)
    (x : X) : X.ord b x = (m : ℤ) * X.ord c x := by
  subst hb
  rw [← zpow_natCast c m, AlgebraicGeometry.Divisors.FunctionFieldOrderPowers.ord_zpow hc]

/-- Divisibility of the order of a power: `b = c ^ m` with `c ≠ 0` implies `(m : ℤ) ∣ ord_x b`.
This is the integrality `ord_y(b_{α,i,q}) / q ∈ ℤ` from the proof of Lemma 3.1 of the paper. -/
theorem ord_dvd_of_eq_pow {b c : X.functionField} (hc : c ≠ 0) {m : ℕ} (hb : b = c ^ m)
    (x : X) : (m : ℤ) ∣ X.ord b x :=
  ⟨X.ord c x, ord_eq_mul_of_eq_pow hc hb x⟩

end
