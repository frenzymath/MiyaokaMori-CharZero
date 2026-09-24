import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra

/-! # The jet neighbourhood `C̃_(κ)(L)`

`C̃_(κ)(L) := Spec_{C̃}(⊕_{q=0}^{κ} L^{-q})`, the `κ`-th infinitesimal neighbourhood of the zero section in
`Tot(L)`, together with its projection `p_L` to the curve (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The jet neighbourhood `C̃_(κ)(L) = Spec_{C̃}(⊕_{q ≤ κ} L^{-q})`, as a scheme over the curve. -/
noncomputable def jetNeighborhood {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) : CategoryTheory.Over Ct.toScheme :=
  AlgebraicGeometry.Scheme.relativeSpec (truncatedJetAlgebra L κ)

/-- The projection `p_L : C̃_(κ)(L) → C̃`. -/
noncomputable abbrev jetNeighborhood.proj {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) : (jetNeighborhood L κ).left ⟶ Ct.toScheme :=
  (jetNeighborhood L κ).hom

end
