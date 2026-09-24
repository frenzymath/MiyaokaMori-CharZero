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
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineConeAffineHom
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConeScalingAction
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ScalarJet

/-! # Generically scalar jets

A based jet is *generically scalar* if there is a nonempty open `U ⊆ C̃` over which `ȷ` equals `s ∘ ρ ∘ p_L`
multiplied by a unit of the truncated algebra with constant term `1` (§3 of the paper: scalarity at the generic
point is equivalent to scalarity over some nonempty open set).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A based jet `J` is generically scalar if over some nonempty open `U ⊆ C̃` it is `u · (s ∘ ρ ∘ p_L)` for a
unit `u` on `p_L⁻¹U` restricting to `1` along the zero section. -/
def BasedJet.IsGenericallyScalar {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    (J : BasedJet f ρ L κ) : Prop :=
  ∃ U : ρ.source.toScheme.Opens, (U : Set ρ.source.toScheme).Nonempty ∧
    ∃ u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤)ˣ,
      -- `u` restricts to `1` along the zero section over `U` (a unit of the truncated algebra with constant term `1`)
      ((jetNeighborhood.zeroSection L κ).resLE ((jetNeighborhood.proj L κ) ⁻¹ᵁ U) U
          (by
            change U ≤ (jetNeighborhood.zeroSection L κ ≫ jetNeighborhood.proj L κ) ⁻¹ᵁ U
            rw [jetNeighborhood.zeroSection_proj]
            exact le_rfl)).appTop
          (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤)) = 1 ∧
      -- over `U`, `J = u · (s ∘ ρ ∘ p_L)`
      ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ J.hom
        = TwistedCone.scale f u
            (((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ jetNeighborhood.proj L κ ≫ ρ.hom
              ≫ (MMSetup.seed f).1)

end
