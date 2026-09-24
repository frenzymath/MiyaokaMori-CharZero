import MiyaokaMori.Paper.S1Intro.TangentBundlePullback

/-! # Positivity of the slope bound

Statement: if `deg(f^*T_X) > 0` and `1 ≤ κ`, then `(deg(f^*T_X) * harmonic κ) / (2 * (dim X + 1) * κ)` is positive.

Proof: cast the integer degree and the positive integer `κ` to `ℚ`; positivity follows from `hd` and `hκ`;
`harmonic_pos` gives `harmonic κ > 0`, and every factor of the denominator is positive, so `div_pos` applies
(§3 of the paper, Proposition 3.2).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem positive_line_threshold_pos {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme)
    (hd : 0 < TangentBundle.pullbackDegree f) (κ : ℕ) (hκ : 1 ≤ κ) :
    0 < ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ) /
      (2 * ((X.toVariety.dim : ℚ) + 1) * κ) := by
  have hdq : (0 : ℚ) < (TangentBundle.pullbackDegree f : ℚ) := by
    exact_mod_cast hd
  have hκ0 : κ ≠ 0 := by omega
  have hhκ : (0 : ℚ) < harmonic κ := harmonic_pos hκ0
  have hnum : (0 : ℚ) < (TangentBundle.pullbackDegree f : ℚ) * harmonic κ :=
    mul_pos hdq hhκ
  have hkq : (0 : ℚ) < (κ : ℚ) := by
    exact_mod_cast (show 0 < κ by omega)
  have hden : (0 : ℚ) < 2 * ((X.toVariety.dim : ℚ) + 1) * (κ : ℚ) := by
    positivity
  exact div_pos hnum hden

end
