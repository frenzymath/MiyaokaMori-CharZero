import MiyaokaMori.Prelude

/-! # A dimension identity for the weighted projectivization

If `1 ≤ kk`, the total dimension of the weighted projectivization satisfies `(n + 1) * kk = 1 + ((n + 1) * kk - 1)`.
Immediate from `kk ≠ 0` and natural number arithmetic.
-/

set_option autoImplicit false

theorem weighted_dimension_eq_succ_sub_one {n kk : ℕ} (hkk : 1 ≤ kk) :
    (n + 1) * kk = 1 + ((n + 1) * kk - 1) := by
  have hpos : 0 < (n + 1) * kk := Nat.mul_pos (Nat.succ_pos n) (by omega)
  omega
