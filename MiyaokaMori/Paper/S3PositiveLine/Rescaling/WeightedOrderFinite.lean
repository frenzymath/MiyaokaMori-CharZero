import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrderTop

/-! # Finiteness of the weighted order

`β_z` is finite: the rational tuple is nonzero, so some `a_{i,q} ≠ 0` and the set over which the minimum is
taken is nonempty (§3 of the paper: "the minimum is finite because the rational tuple is nonzero").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The weighted order of a nonzero tuple is finite (`≠ ⊤`). The proof is done in `WeightedOrderTop` for a
general integral locally Noetherian scheme (`weightedOrderTop_ne_top`, a consequence of "the minimum is attained
at some nonzero coordinate"); this is the specialization to curves. -/
theorem weightedOrder_finite {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    {n κ : ℕ} (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0) (z : Ct.toScheme) :
    weightedOrderTop a z ≠ ⊤ :=
  weightedOrderTop_ne_top a hne z

end
