import MiyaokaMori.Prelude

/-! # The bound `δ·r₀ < k`

`δ·r₀ < k`: from `δ·r₀ ≤ δae/d_L` and the inequality `δ·a·e < k·d_L` given by the positive slope
(equation (4.3) in the proof of Theorem 4.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem delta_r0_lt_k {a e dL : ℤ} {δ κ : ℕ}
    (hdL : 0 < dL) (he : 0 < e) (ha : 0 ≤ a)
    (hslope : (δ : ℤ) * a * e < (κ : ℤ) * dL) :
    (δ : ℤ) * (a * e / dL) < (κ : ℤ) := by
  have hfloor : (a * e / dL) * dL ≤ a * e := by
    exact (Int.le_ediv_iff_mul_le hdL).1 (le_refl (a * e / dL))
  have hδ : 0 ≤ (δ : ℤ) := by positivity
  have hmul : (δ : ℤ) * ((a * e / dL) * dL) ≤ (δ : ℤ) * (a * e) :=
    Int.mul_le_mul_of_nonneg_left hfloor hδ
  have hchain : (δ : ℤ) * ((a * e / dL) * dL) < (κ : ℤ) * dL := by
    exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hslope
  have hright : ((δ : ℤ) * (a * e / dL)) * dL < (κ : ℤ) * dL := by
    simpa [mul_assoc] using hchain
  exact (Int.mul_lt_mul_right hdL).mp (by simpa [mul_assoc] using hright)

end
