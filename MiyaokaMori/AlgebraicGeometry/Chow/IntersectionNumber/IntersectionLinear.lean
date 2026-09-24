import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOverCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeSeparated
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStandardChart
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveNormalization
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseClosedPoint
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineConeAffineHom
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSchemeAffineOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.GenericSaturationSubsheaf
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothVarietyRegularInCodimOne

/-! # Linearity of the intersection number in the one-cycle

The intersection number of a line bundle with a one-cycle is linear in the cycle:
`L ⬝ (Σ a_i [Γ_i]) = Σ a_i (L ⬝ Γ_i)` (equation (5.1) of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem inter_sum {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    (L : LineBundle X.toVariety) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (Γ : ι → IntegralCurve k X.toScheme) :
    L ⬝ (∑ i ∈ s, a i • (Γ i).fundamentalClass) = ∑ i ∈ s, a i * (L ⬝ (Γ i).fundamentalClass) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact L.interHom.map_zero
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.sum_add_distrib, Finset.sum_smul]
      change L.interHom (a i • (Γ i).fundamentalClass +
        ∑ i ∈ s, a i • (Γ i).fundamentalClass) = _
      rw [map_add, map_zsmul]
      rw [show L.interHom (∑ i ∈ s, a i • (Γ i).fundamentalClass) =
          ∑ i ∈ s, a i * (L ⬝ (Γ i).fundamentalClass) by
        simpa [LineBundle.inter] using ih]
      change a i * L.interHom (Γ i).fundamentalClass +
          ∑ i ∈ s, a i * (L ⬝ (Γ i).fundamentalClass) =
        a i * L.interHom (Γ i).fundamentalClass +
          ∑ i ∈ s, a i * (L ⬝ (Γ i).fundamentalClass)
      rfl

end
