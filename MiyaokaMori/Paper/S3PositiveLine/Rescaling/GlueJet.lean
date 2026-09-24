import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalCoordinates
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetTransition
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FrameChangeNormalization
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.NormalizeCoefficients

/-! # Gluing local jets

Local jets glue to a global morphism `ȷ : C̃_(k)(L) → 𝒵` over `ρ` with `ȷ|_C̃ = s∘ρ` (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The data of the local jets are written directly as a family of morphisms on an open cover: `g i` is a
   `C`-morphism (over) from the `i`-th piece of `𝒰` to the cone `𝒵`, the pieces agree on overlaps (`hcompat`), and
   the restriction along the zero section of the jet is the seed `s∘ρ` (`hrestrict`); conclusion: they glue to a based jet. -/

theorem exists_glued_jet {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (L : LineBundle ρ.source.toVariety)
    (𝒰 : (jetNeighborhood L κ).left.OpenCover)
    (g : ∀ i, 𝒰.X i ⟶ (MMSetup.cone f).left)
    (hcompat : ∀ i j, CategoryTheory.Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i
        = CategoryTheory.Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j)
    (hover : ∀ i, g i ≫ (MMSetup.cone f).hom = 𝒰.f i ≫ jetNeighborhood.proj L κ ≫ ρ.hom)
    (hrestrict : ∀ i,
      CategoryTheory.Limits.pullback.snd (jetNeighborhood.zeroSection L κ) (𝒰.f i) ≫ g i
        = CategoryTheory.Limits.pullback.fst (jetNeighborhood.zeroSection L κ) (𝒰.f i)
            ≫ ρ.hom ≫ (MMSetup.seed f).1) :
    ∃ J : BasedJet f ρ L κ, ∀ i, 𝒰.f i ≫ J.hom = g i := by
  let j : (jetNeighborhood L κ).left ⟶ (MMSetup.cone f).left :=
    𝒰.glueMorphisms g hcompat
  have hj : ∀ i, 𝒰.f i ≫ j = g i := by
    intro i
    exact 𝒰.ι_glueMorphisms g hcompat i
  have hoverj : j ≫ (MMSetup.cone f).hom = jetNeighborhood.proj L κ ≫ ρ.hom := by
    apply 𝒰.hom_ext
    intro i
    rw [← Category.assoc, hj i]
    exact hover i
  have hrestrictj : jetNeighborhood.zeroSection L κ ≫ j = ρ.hom ≫ (MMSetup.seed f).1 := by
    apply AlgebraicGeometry.Scheme.Cover.hom_ext
      (𝒰.pullback₁ (jetNeighborhood.zeroSection L κ))
    intro i
    change pullback.fst (jetNeighborhood.zeroSection L κ) (𝒰.f i) ≫
        jetNeighborhood.zeroSection L κ ≫ j =
      pullback.fst (jetNeighborhood.zeroSection L κ) (𝒰.f i) ≫
        ρ.hom ≫ (MMSetup.seed f).1
    rw [pullback.condition_assoc]
    rw [hj (i : 𝒰.I₀)]
    exact hrestrict (i : 𝒰.I₀)
  refine ⟨⟨j, hoverj, hrestrictj⟩, hj⟩

end
