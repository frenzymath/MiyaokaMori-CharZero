import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeSeparated
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ConnectedScheme
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CurveDegreeIntersectionCompat
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.Paper.S3PositiveLine.Realization.RuledSurface
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerIsOver
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupsAvoidSection
import MiyaokaMori.AlgebraicGeometry.Blowup.EliminationOfIndeterminacy
import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberDegreeBetween
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberRestriction
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.GeneralFiberAvoidsFiniteSet
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.PullbackDegreeFiniteCover
import MiyaokaMori.AlgebraicGeometry.Morphisms.RationalMapPrecomp
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupPreservesConnected
import MiyaokaMori.Paper.S4Completion.FiberOneCycle
import MiyaokaMori.Paper.S4Completion.GeneralFiberDegree
import MiyaokaMori.Paper.S4Completion.RuledSurfaceFiberP1

import MiyaokaMori.AlgebraicGeometry.Morphisms.ResolvedSurfaceGeneralFiber
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerSurjective
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerFiberConnected
import MiyaokaMori.Paper.S3PositiveLine.Realization.RuledSurfaceFiberConnected
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionLiftOverOpen
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsOverOfAgreeDense
/-! # The resolved surface

The resolution `S`: for a rational map `W = P(O⊕L) ⇢ X` regular on a neighbourhood `U` of the zero section, a tower
of point blowups `β : S → W` with centres away from `U` yields a smooth connected projective surface `S`,
`π_S = π_W∘β` (surjective, with connected closed fibers), a section `σ` and `Φ : S → X` with `Φ∘σ = f∘ρ`; the
general closed fiber is `≅ P¹` with `1 ≤ deg(Φ^*O_X(1)|_F) ≤ r₀` (Corollary 4.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem resolved_surface {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {r₀ : ℕ}
    (Φ₀ : (ruledSurface L).toScheme ⤏ X.toScheme)
    [Φ₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : (ruledSurface L).toScheme.Opens) (hU : IsRegularOn Φ₀ U)
    (σ₀ : ρ.source.toScheme ⟶ U.toScheme)
    (hσ₀ : σ₀ ≫ U.ι ≫ ruledSurface.π L = CategoryTheory.CategoryStruct.id _)
    (hσΦ : σ₀ ≫ (ruledSurface L).toScheme.homOfLE hU ≫ Φ₀.toPartialMap.hom = ρ.hom ≫ f)
    (hdeg : ∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
        ∃ (e : ((ruledSurface.π L).fiber y)
              ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme)
          (Φy : ((ruledSurface.π L).fiber y) ⟶ X.toScheme),
          AgreesOnOpen Φy ((ruledSurface L).toScheme.homOfLE hU ≫ Φ₀.toPartialMap.hom)
            ((ruledSurface.π L).fiberι y) (CategoryTheory.CategoryStruct.id _) ∧
          1 ≤ (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety) (e.inv ≫ Φy) (X.OX 1)).degree ∧
          (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety) (e.inv ≫ Φy) (X.OX 1)).degree ≤ (r₀ : ℤ)) :
    ∃ (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ (ruledSurface L).toScheme)
      (_ : IsBlowupTower β)
      (_ : IsBlowupTowerAvoiding β (U : Set (ruledSurface L).toScheme))
      (πS : S.toScheme ⟶ ρ.source.toScheme)
      (hπS : AlgebraicGeometry.Surjective πS)
      (σ : ρ.source.toScheme ⟶ S.toScheme) (Φ : S.toScheme ⟶ X.toScheme),
      πS = β ≫ ruledSurface.π L ∧
      (∀ y : ρ.source.toScheme, IsClosed ({y} : Set ρ.source.toScheme) →
        _root_.IsConnected (πS.base ⁻¹' {y})) ∧
      σ ≫ πS = CategoryTheory.CategoryStruct.id ρ.source.toScheme ∧
      σ ≫ β = σ₀ ≫ U.ι ∧
      σ ≫ Φ = ρ.hom ≫ f ∧
      Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      ∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
        ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
          Nonempty ((πS.fiber y) ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) ∧
          1 ≤ fiberDegree πS hπS (LineBundle.pullback Φ (X.OX 1)) y ∧
          fiberDegree πS hπS (LineBundle.pullback Φ (X.OX 1)) y ≤ (r₀ : ℤ) := by
  have : X.toScheme.IsSeparated :=
    AlgebraicGeometry.Scheme.isSeparated_of_isProper_over_field (k := k) X.toScheme
  obtain ⟨S, β, hβ, havoid, hβd, Ψ, -, hiso, hagree⟩ :=
    elimination_avoiding_regular_locus (ruledSurface L) X.toScheme X.projective Φ₀ U hU
  obtain ⟨σ, hσβ, hσlift⟩ := AlgebraicGeometry.exists_lift_of_isIso_morphismRestrict β U hiso σ₀
  have : AlgebraicGeometry.Surjective β := hβ.surjective
  have hπS : AlgebraicGeometry.Surjective (β ≫ ruledSurface.π L) := inferInstance
  have hβover : β.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := hβ.isOver
  have hdense : Dense ((β ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme) := by
    obtain ⟨y⟩ : Nonempty ρ.source.toScheme := inferInstance
    exact (β ⁻¹ᵁ U).2.dense ⟨σ y, by
      show β.base (σ.base y) ∈ U
      have h := congrArg (fun m => m.base y) hσβ
      simp only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [h]
      exact (σ₀.base y).2⟩
  refine ⟨S, β, hβ, havoid, β ≫ ruledSurface.π L, hπS, σ, Ψ, rfl, ?_, ?_, hσβ, ?_, ?_, ?_⟩
  · intro y hy
    exact hβ.fiber_connected (ruledSurface.π L) y hy
      (ruledSurface.fiber_preimage_isConnected L y hy)
  · rw [← Category.assoc, hσβ, Category.assoc, hσ₀]
  · rw [hσlift Ψ _ hagree, hσΦ]
  · refine AlgebraicGeometry.Scheme.Hom.isOver_of_agree_on_dense Ψ (β ⁻¹ᵁ U) hdense ?_
    haveI := hβover
    exact AlgebraicGeometry.Scheme.Hom.comp_over_of_agree β U Φ₀.domain hU Ψ Φ₀.toPartialMap.hom
      (AlgebraicGeometry.Scheme.PartialMap.isOver_iff.mp inferInstance) hagree
  · exact resolved_surface_general_fiber Φ₀ U hU hdeg S β hβ havoid Ψ hagree hπS

end
