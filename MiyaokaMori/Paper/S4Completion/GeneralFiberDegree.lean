import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveAsSmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.Paper.S4Completion.FiberOneCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection

/-! # The degree of a line bundle on a fibre

The fibre degree `d_F = A_S · F_y`: the intersection number of a line bundle `A_S` on the surface `S`
with the fibre cycle `F_y = [π^*(y)]` (see Lemma 5.1 of the paper, §5, where
`A_S = Φ^* O_X(1)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The intersection number `A · [π^*(y)]` of the line bundle `A` on `S` with the fibre cycle over `y`. -/
noncomputable def fiberDegree {k : Type u} [Field k] [IsAlgClosed k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (A : LineBundle S.toVariety) (y : C.toScheme) : ℤ :=
  LineBundle.inter (X := S.toSmoothProjectiveVariety) A (fiberCycle π hπ y)

end
