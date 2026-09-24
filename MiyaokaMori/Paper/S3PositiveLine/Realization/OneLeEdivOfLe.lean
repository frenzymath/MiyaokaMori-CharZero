import MiyaokaMori.Prelude

/-! # An integer division bound

`0 < b` and `b ≤ a` imply `1 ≤ a/b` (instantiate `Int.le_ediv_iff_mul_le` at `q = 1` and cancel `1 * b` by `one_mul`);
used in the proof of Theorem 4.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem one_le_ediv_of_le {a b : ℤ} (hb : 0 < b) (hab : b ≤ a) : 1 ≤ a / b := by
  apply (Int.le_ediv_iff_mul_le hb).2
  simpa using hab

end
