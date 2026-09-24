import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupPreservesConnected

/-! # Towers of point blowups preserve connected fibres

A tower of point blowups preserves the connectedness of the fibres over closed points of a curve
(induction along the tower; the single-step case is `blowup_fiber_connected`). "Point blowups preserve
connectedness of the fibers", proof of Corollary 4.3 of the paper (§4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- If the fibre of `π : W → C` over a closed point `y` is connected, so is the fibre of `β ≫ π` for every
tower of point blowups `β : S → W`. -/
theorem IsBlowupTower.fiber_connected {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme} (hβ : IsBlowupTower β) :
    ∀ {C : SmoothProjectiveCurve k} (π : W.toScheme ⟶ C.toScheme) (y : C.toScheme)
      (_ : IsClosed ({y} : Set C.toScheme)) (_ : _root_.IsConnected (π.base ⁻¹' {y})),
      _root_.IsConnected ((β ≫ π).base ⁻¹' {y}) := by
  induction hβ with
  | id W =>
    intro C π y hy h
    rwa [Category.id_comp]
  | step g hg p hp ih =>
    intro C π y hy h
    rw [Category.assoc]
    exact blowup_fiber_connected (g ≫ π) p hp y hy (ih π y hy h)

end
