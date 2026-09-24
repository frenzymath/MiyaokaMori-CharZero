import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.PositiveLineArithmetic
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCore

/-! # A jet on a positive line

For every `k ≥ 1` there exist a finite cover `ρ : C̃ → C`, a line bundle `L` on `C̃` and a generically nonscalar
based jet `ȷ` over `ρ` whose tuple of positive-order coefficients is nowhere zero, with
`d_L/e > d h_k/(2(n+1)k) > 0`.

In the paper this statement is the composite of Lemma 2.5 (`Targets/NegativeHorizontalCurve.lean`),
Lemma 3.1 (`Targets/AffineLiftAfterBaseChange.lean`) and the slope bound of
Proposition 3.2 (`Targets/InverseTautologicalClass.lean`, `τ^*O(m) ≃ L^{-m}`): the existence of `ρ`, `L`,
`ȷ` with nowhere-zero tuple, generically nonscalar, and `deg L / deg ρ > d h_k /(2(n+1)k)`. The generic-nonscalar
clause is the nonconstant-projection part of Lemma 4.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **A jet on a positive line**: existence of `ρ`, `L` and a based jet `J` with nowhere-zero normalized tuple, not
generically scalar, and slope `deg L / deg ρ > d h_κ / (2(n+1)κ) > 0`. -/
theorem positive_line {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (hf : ¬ IsConstantMorphism f)
    (hd : 0 < TangentBundle.pullbackDegree f) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∃ (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ),
      NormalizedTupleNowhereZero J ∧
      ¬ J.IsGenericallyScalar ∧
      (L.degree : ℚ) / (ρ.degree : ℚ)
        > ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)
            / (2 * ((X.toVariety.dim : ℚ) + 1) * κ) ∧
      0 < ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)
            / (2 * ((X.toVariety.dim : ℚ) + 1) * κ) := by
  have hthreshold := positive_line_threshold_pos f hd κ hκ
  rcases positive_line_core f hf hd κ hκ with ⟨ρ, L, J, hnz, hns, hslope⟩
  exact ⟨ρ, L, J, hnz, hns, hslope, hthreshold⟩

end
