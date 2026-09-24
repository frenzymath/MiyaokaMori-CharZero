import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.NumericalEquivalence

/-! # Numerically equivalent one-cycles have the same intersection numbers

Numerically equivalent one-cycles have the same intersection number with every line bundle
(immediate from the definition). Used in §4 of the paper (the fibers of the ruled surface are
numerically equivalent). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem inter_eq_of_numEquiv {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    (L : LineBundle X.toVariety) {Z W : OneCycle X.toVariety} (h : Z.NumEquiv W) :
    L ⬝ Z = L ⬝ W := by
  exact h L

end
