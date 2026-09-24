import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePushforward

/-! # The degree of a zero-cycle as a sum (Stacks 0AZ2)

Stacks 0AZ2: for `X` proper over `k`, the degree of a zero-cycle `α = Σ n_i[Z_i]` is
`deg α = Σ n_i·deg(Z_i)` with `deg(Z_i) = dim_k Γ(Z_i, O) = [κ(z_i):k]` (the definition of the
pushforward to `Spec k`, spelled out). Since `ChowGroup.degree` is defined as the scheme-level
`degreeOver` (`AlgebraicCycle.degree` is `∑ᶠ x, c x * residueDegree (X ↘ Spec k) x`, descended to the
quotient), the sum formula holds by definition (`QuotientAddGroup.lift_mk` is `rfl`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem ChowGroup.degree_mk {k : Type*} [Field k] [IsAlgClosed k] (X : SmoothProjectiveVariety k)
    (α : CycleGroup X.toVariety 0) :
    ChowGroup.degree X (QuotientAddGroup.mk α)
      = ∑ᶠ x : X.toScheme, (α : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) x *
          ((AlgebraicGeometry.Scheme.Hom.residueDegree X.structureMorphism x : ℕ) : ℤ) := by
  -- by definition, `degreeOver` is `AlgebraicCycle.degree` descended through `QuotientAddGroup.lift`,
  -- `AlgebraicCycle.degree α = ∑ᶠ x, α x * residueDegree (X.toScheme ↘ Spec k) x`, and
  -- `X.structureMorphism` is `X.toScheme ↘ Spec k` (`Variety.structureMorphism` is an abbrev).
  rfl

end
