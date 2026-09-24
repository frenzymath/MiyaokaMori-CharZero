import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.SeedBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceRestrictToZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.NonconstantMorphism
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.Paper.S3PositiveLine.Realization.RuledSurface
import MiyaokaMori.Paper.S2WeightedJets.Cone.TotLineAffineOverBase
import MiyaokaMori.AlgebraicGeometry.Morphisms.TotalSpaceAgreesTotLine
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberRestriction
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberPolynomialExtensionDegree
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalar
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroSection
import MiyaokaMori.Paper.S3PositiveLine.Realization.NonconstantOnGeneralFiber
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.P1MapDegreeFromPolynomials
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMinors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.PullbackDegreeFiniteCover
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.Paper.S4Completion.RuledSurfaceFiberP1

/-! # The degree on a general ruled fiber lies in `[1, r₀]`

After homogenization, the `O_X(1)`-degree on a general fiber of the ruled surface lies in `[1, r₀]`: there is a
nonempty open `V ⊆ C̃` such that over every closed point `y ∈ V` the fiber `W_y ≅ P¹` carries a morphism `Φ_y`
agreeing with `Φ₀` on a nonempty open, with `1 ≤ deg Φ_y^*O_X(1) ≤ r₀` (upper bound from the homogenization,
lower bound from nonconstancy); proof of Theorem 4.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

def AgreesOnOpen {A S T Z : AlgebraicGeometry.Scheme.{u}} {U : T.Opens}
    (g : A ⟶ Z) (Φ₀ : U.toScheme ⟶ Z) (incl : A ⟶ S) (ι : T ⟶ S) : Prop :=
  ∃ (O : A.Opens) (_ : O ≠ ⊥) (j : O.toScheme ⟶ U.toScheme),
    j ≫ U.ι ≫ ι = O.ι ≫ incl ∧ j ≫ Φ₀ = O.ι ≫ g

theorem fiber_degree_between {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ r₀ : ℕ} (jet : BasedJet f ρ L κ)
    (hns : ¬ jet.IsGenericallyScalar)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L (seedBundlePullback f ρ) (P ℓ)
      ≤ (r₀ : WithBot ℕ))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ
        = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ)
      = seedCoordPullback f ρ (D.coord ℓ))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Φ₀ : U.toScheme ⟶ X.toScheme) (hΦ : IsTupleProjectivization _ P U Φ₀)
    (hU0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base
      ⊆ (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)) :
    ∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
    ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
      ∃ (e : ((ruledSurface.π L).fiber y)
            ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme)
        (Φy : ((ruledSurface.π L).fiber y) ⟶ X.toScheme),
        AgreesOnOpen Φy Φ₀ ((ruledSurface.π L).fiberι y) (ruledSurface.totalSpaceIncl L) ∧
        1 ≤ (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety) (e.inv ≫ Φy) (X.OX 1)).degree ∧
        (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety) (e.inv ≫ Φy) (X.OX 1)).degree ≤ (r₀ : ℤ) := by
  obtain ⟨_, V, hVopen, hVne, hV⟩ :=
    nonconstant_on_general_fiber jet hns P hjet hzero U Φ₀ hΦ hU0
  refine ⟨V, hVopen, hVne, ?_⟩
  intro y hy hyclosed
  obtain ⟨e, Φy, O, hOne, j, hjfiber, hjΦ, hlow, hupp⟩ :=
    fiber_polynomial_extension_degree jet P hP hjet hzero U Φ₀ hΦ hU0 y hyclosed
      (by simpa using hV y hy hyclosed)
  refine ⟨e, Φy, ?_, hlow, hupp⟩
  exact ⟨O, hOne, j, hjfiber, hjΦ⟩

end
