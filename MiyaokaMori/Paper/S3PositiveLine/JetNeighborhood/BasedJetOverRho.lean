import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.TopcatSheafOpenClosedFunctors
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
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # Based jets over a finite cover

A *based jet over `ρ`* is a morphism `ȷ : C̃_(κ)(L) → 𝒵` from the jet neighbourhood to the twisted cone
satisfying `p_𝒵 ∘ ȷ = ρ ∘ p_L` and `ȷ|_C̃ = s ∘ ρ` (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A based jet of order `κ` over the finite cover `ρ : C̃ → C`, carried by the line bundle `L` on `C̃`: a
morphism `hom : C̃_(κ)(L) → 𝒵` compatible with the projections to `C` (`over`) and restricting to the seed
section `s ∘ ρ` along the zero section (`restrict`). -/
structure BasedJet {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) [MMSetup f]
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (κ : ℕ) where
  hom : (jetNeighborhood L κ).left ⟶ (MMSetup.cone f).left
  «over» : hom ≫ (MMSetup.cone f).hom = jetNeighborhood.proj L κ ≫ ρ.hom
  restrict : jetNeighborhood.zeroSection L κ ≫ hom = ρ.hom ≫ (MMSetup.seed f).1

end
