import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceRestrictToZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismImageAsRange
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeOpen
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback

/-! # The morphism near the zero section: the data

Two predicates used in the proof of Theorem 4.2 of the paper: `IsTupleProjectivization` says that a
morphism `Φ₀ : U → X` on an open `U` of a scheme `T` is the projectivization of a tuple `P` of sections of a line
bundle `M` (composed with the projective embedding of `X`); `RealizesJet` says that a morphism `Φ₀` on an open
neighbourhood `U` of the zero section of `Tot(L)` realizes a based jet: on the zero section it is `f∘ρ`, and on the jet
neighbourhood it is the projection of the jet (viewed in the punctured cone) to `X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Φ₀ : U → X` is the projectivization of the tuple `P` of sections of the line bundle `M`: the restrictions of the
`P_ℓ` to `U` have no common zero, and `Φ₀` composed with the embedding `X ↪ P^N` is the morphism `U → P^N` given by
this nowhere-zero tuple (`projectivizationMorphism`). -/
def IsTupleProjectivization {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {T : AlgebraicGeometry.Scheme.{u}} [T.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : T.Modules) [M.IsLineBundle]
    (P : Fin (X.embDim + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (U : T.Opens) (Phi0 : U.toScheme ⟶ X.toScheme) : Prop :=
  ∃ hU : ∀ v : U.toScheme, ∃ ℓ, ¬ IsZeroAt (sectionPullbackAlong U.ι (P ℓ)) v,
    Phi0 ≫ X.embedding.emb =
      projectivizationMorphism (k := k) ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M)
        (fun ℓ ↦ sectionPullbackAlong U.ι (P ℓ)) hU

/-- `Φ₀ : U → X`, defined on an open `U` of `Tot(L)`, realizes the based jet `jet`: `U` contains the zero section, and
there are lifts `sigma0` of the zero section and `nu` of the jet neighbourhood `C̃_(κ)(L)` to `U`, and a factorization
`jetx` of the jet through the punctured cone `Z^×`, such that `Φ₀` restricted to the zero section is `ρ ≫ f` and `Φ₀`
restricted to the jet neighbourhood is `jetx ≫ (Z^× → X)`. -/
def RealizesJet {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {rho : FiniteCover k C}
    {L : LineBundle rho.source.toVariety} {kappa : ℕ} (jet : BasedJet f rho L kappa)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Phi0 : U.toScheme ⟶ X.toScheme) : Prop :=
  Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base
      ⊆ (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left) ∧
    ∃ (sigma0 : rho.source.toScheme ⟶ U.toScheme)
      (nu : (jetNeighborhood L kappa).left ⟶ U.toScheme)
      (jetx : (jetNeighborhood L kappa).left ⟶ (MMSetup.punctured f).toScheme),
      sigma0 ≫ U.ι = AlgebraicGeometry.Scheme.zeroSection L.toModules ∧
      sigma0 ≫ Phi0 = rho.hom ≫ f ∧
      jetx ≫ (MMSetup.punctured f).ι = jet.hom ∧
      nu ≫ Phi0 = jetx ≫ MMSetup.toX f

end
