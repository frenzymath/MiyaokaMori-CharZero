import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Realization.OneLeEdivOfLe

/-! # The bound `r₀ ≥ 1`

`r₀ = ⌊ae/d_L⌋ ≥ 1` as soon as `0 < d_L ≤ ae` (the latter follows from some coefficient of order `q ≥ 1` being
nonzero); proof of Theorem 4.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem r0_ge_one {a e dL : ℤ} (hdL : 0 < dL) (h : dL ≤ a * e) :
    1 ≤ a * e / dL := by
  exact one_le_ediv_of_le hdL h

end
