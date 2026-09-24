import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

/-! # The common multiple of the jet weights

`jetWeight k = lcm(1, …, k)` is the common multiple `w_k` of the jet weights `1, …, k`
used in the Veronese polarization of the weighted projectivization
(Lemma 2.2 of the paper).

This file imports only Mathlib, so that it can be used below the project's prelude.
-/

set_option autoImplicit false

noncomputable section

/-- The common multiple `w_k = lcm(1, …, k)` of the jet weights of order `≤ k`. -/
def jetWeight (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

end
