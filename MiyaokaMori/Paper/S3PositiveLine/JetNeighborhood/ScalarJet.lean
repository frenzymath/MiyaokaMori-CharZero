import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConeScalingAction
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection

/-! # Scalar jets

A based jet `ȷ` is *scalar* if it equals `s ∘ ρ ∘ p_L` multiplied by a unit of the truncated algebra whose
constant term is `1` (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A based jet `J : C̃_(κ)(L) → 𝒵` over `ρ` is scalar if `J = u · (s ∘ ρ ∘ p_L)` for a global unit `u` of
`C̃_(κ)(L)` restricting to `1` along the zero section. -/
def BasedJet.IsScalar {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    (J : BasedJet f ρ L κ) : Prop :=
  ∃ u : Γ((jetNeighborhood L κ).left, ⊤)ˣ,
    (jetNeighborhood.zeroSection L κ).appTop (u : Γ((jetNeighborhood L κ).left, ⊤)) = 1 ∧
    J.hom = TwistedCone.scale f u (jetNeighborhood.proj L κ ≫ ρ.hom ≫ (MMSetup.seed f).1)

end
