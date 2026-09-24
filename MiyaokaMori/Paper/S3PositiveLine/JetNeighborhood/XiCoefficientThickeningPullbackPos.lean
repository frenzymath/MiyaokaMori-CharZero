import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalarOfCoefficientsZero
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # Positive `ξ`-coefficients of a pulled-back section vanish

The positive-order `ξ`-coefficients of a section pulled back from the curve to the jet neighbourhood vanish:
`p_κ^* t` is "constant along the fibres", so only its `q = 0` coefficient is nonzero.

This is the shape of the constant term `ρ^*f_ℓ` in the expansion (4.1) of
Lemma 4.1 of the paper: a pulled-back section has `c_q = 0` for `q ≥ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Positive coefficients of a pulled-back section vanish.** For `1 ≤ q` and `t ∈ Γ(C̃, M)`,
`xiCoefficientThickening L M κ q (p_κ^* t) = 0`.

Proof. If `q > κ` this is the definition (`xiCoefficientThickening` is `0` there). If `q ≤ κ`:
`p_κ^* t = restrictToThickening L M κ (p_L^* t)` (`restrictToThickening_sectionPullbackAlong`), and restriction to
the thickening does not change coefficients of order `≤ κ` (`xiCoefficient_restrictToThickening`), so the
coefficient is `xiCoefficient L M (p_L^* t) q` on `Tot(L)`. Now `p_L^* t` is the degree-`0` monomial
`xiMonomial L M 0 c` with `c = (coefficientZeroIso L M).inv t` (`xiMonomial_zero_eq_sectionPullbackAlong`), whose
`q`-th coefficient is `0` for `q ≠ 0` (`xiCoefficient_xiMonomial`). -/
theorem xiCoefficientThickening_sectionPullbackAlong_of_pos {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L M : LineBundle Ct.toVariety) (κ q : ℕ) (hq : 1 ≤ q)
    (t : (M.toModules.val.obj (Opposite.op ⊤) : Type u)) :
    xiCoefficientThickening L M κ q (sectionPullbackAlong (jetNeighborhood.proj L κ) t) = 0 := by
  by_cases hqκ : q ≤ κ
  · rw [← restrictToThickening_sectionPullbackAlong L M κ t,
      xiCoefficient_restrictToThickening L M κ q hqκ]
    have h0 := xiMonomial_zero_eq_sectionPullbackAlong L M
      (((coefficientZeroIso L M).inv.val.app (Opposite.op ⊤)).hom t)
    rw [AlgebraicGeometry.Scheme.Modules.app_top_inv_hom] at h0
    rw [← h0, xiCoefficient_xiMonomial, dif_neg (by omega)]
  · unfold xiCoefficientThickening
    rw [dif_neg hqκ]

end
