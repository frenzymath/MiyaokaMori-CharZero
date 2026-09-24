import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S4Completion.RuledSurfaceFiberP1

/-! # Fibers of the ruled surface are connected

The closed fibers of the ruled surface `π_W : P(O⊕L) → C` (as subsets of the underlying space) are connected: each
is the image of an integral curve (`≅ P¹`); used in Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

theorem ruledSurface.fiber_preimage_isConnected {k : Type u} [Field k] [IsAlgClosed k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) (y : C.toScheme)
    (hy : IsClosed ({y} : Set C.toScheme)) :
    _root_.IsConnected ((ruledSurface.π L).base ⁻¹' {y}) := by
  obtain ⟨-, F, hF, -⟩ := ruled_fiber_iso_p1 L y hy
  rw [← hF]
  haveI : AlgebraicGeometry.IsIntegral F.carrier := F.isIntegral
  exact isConnected_range F.ι.base.hom.continuous

end
