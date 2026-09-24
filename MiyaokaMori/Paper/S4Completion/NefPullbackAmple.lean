import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.Paper.S2WeightedJets.Cone.AmpleOXOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.AmpleImpliesNef
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DegreeZeroIffConstant
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.FiberDivisorPullback
import MiyaokaMori.Paper.S4Completion.FiberOneCycle
import MiyaokaMori.Paper.S4Completion.GeneralFiberDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # Nefness of `A_S = Φ^* O_X(1)` and the fibre degree bound

The pullback `A_S = Φ^* O_X(1)` of the ample bundle `O_X(1)` along `Φ : S → X` is nef, and on an
integral fibre component `F` on which `Φ` is nonconstant its degree is positive, `1 ≤ d_F = A_S · F`
(Lemma 5.1 of the paper, §5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Φ^* O_X(1)` is nef, and its degree on an integral curve `F ⊆ S` on which `Φ` is nonconstant is
positive. -/
theorem nef_pullback_ample {k : Type u} [Field k] [IsAlgClosed k] {S : SmoothProjectiveSurface k}
    {X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    IsNef (Φ ^* (X.OX 1)) ∧
    ∀ {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
      (y₀ : C.toScheme) (F : IntegralCurve k S.toScheme),
      fiberCycle π hπ y₀ = F.fundamentalClass →
      ¬ IsConstantMorphism (F.ι ≫ Φ) →
      1 ≤ fiberDegree π hπ (Φ ^* (X.OX 1)) y₀ := by
  have hOX : AlgebraicGeometry.IsAmple (X.OX 1).toModules := ample_OX_one X
  have hnefX : IsNef (X.OX 1) := IsAmple.isNef hOX
  have hnef : IsNef (Φ ^* (X.OX 1)) := IsNef.pullback Φ hnefX
  refine ⟨hnef, ?_⟩
  intro C π hπ y₀ F hF hnc
  have hnonneg : 0 ≤ (Φ ^* (X.OX 1)) ⬝ F.fundamentalClass := hnef F
  have hne : (Φ ^* (X.OX 1)) ⬝ F.fundamentalClass ≠ 0 := by
    intro hz
    exact hnc ((degree_eq_zero_iff_constant Φ hOX F).mp hz)
  have hfd_nonneg : 0 ≤ fiberDegree π hπ (Φ ^* (X.OX 1)) y₀ := by
    rw [show fiberDegree π hπ (Φ ^* (X.OX 1)) y₀ =
        (Φ ^* (X.OX 1)) ⬝ F.fundamentalClass by
      unfold fiberDegree
      rw [hF]]
    exact hnonneg
  have hfd_ne : fiberDegree π hπ (Φ ^* (X.OX 1)) y₀ ≠ 0 := by
    intro hz
    apply hne
    rw [show fiberDegree π hπ (Φ ^* (X.OX 1)) y₀ =
        (Φ ^* (X.OX 1)) ⬝ F.fundamentalClass by
      unfold fiberDegree
      rw [hF]] at hz
    exact hz
  omega

end
