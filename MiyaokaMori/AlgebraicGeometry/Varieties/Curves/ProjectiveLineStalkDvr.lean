import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceChartPolynomial
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ClosedPoint
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveStalkDVR

/-! # Stalks of the projective line at closed points are DVRs

The local rings of `P¹_K` at closed points are discrete valuation rings (they are localizations
of `K[T]` at maximal ideals; used in the proof of Stacks 02RU to show that `q` is flat).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem ProjectiveLine.stalk_isDiscreteValuationRing {K : Type u} [Field K]
    (x : ProjectiveLine K) (hx : IsClosed ({x} : Set (ProjectiveLine K))) :
    ∃ _ : IsDomain ((ProjectiveLine K).presheaf.stalk x),
      IsDiscreteValuationRing ((ProjectiveLine K).presheaf.stalk x) := by
  -- `P¹` is a `SmoothProjectiveCurve` (`ProjectiveLine.asSmoothProjectiveCurve`), and the stalk of a
  -- curve at a closed point is a DVR (`CurveStalkDVR.lean`)
  have : AlgebraicGeometry.IsIntegral (ProjectiveLine.asSmoothProjectiveCurve K).toScheme :=
    SmoothProjectiveCurve.isIntegral _
  have hco : Order.coheight (α := (ProjectiveLine.asSmoothProjectiveCurve K).toScheme) x = 1 :=
    (ProjectiveLine.asSmoothProjectiveCurve K).coheight_eq_one_of_isClosed x hx
  exact ⟨inferInstanceAs (IsDomain
      ((ProjectiveLine.asSmoothProjectiveCurve K).toScheme.presheaf.stalk x)),
    (ProjectiveLine.asSmoothProjectiveCurve K).isDiscreteValuationRing_stalk x hco⟩

end
