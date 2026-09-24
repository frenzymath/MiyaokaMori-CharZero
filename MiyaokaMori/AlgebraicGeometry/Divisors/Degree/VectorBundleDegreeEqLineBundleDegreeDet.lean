import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DeterminantLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil

/-! # The degree of a vector bundle is the degree of its determinant

`VectorBundle.degree E = LineBundle.degree (det E)` for a vector bundle `E` on a smooth projective
curve. Sources: Hartshorne II.6.13, II.6.15; Stacks 02SG, 0AYQ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree of a vector bundle equals the degree of its determinant line bundle. -/
theorem VectorBundle.degree_eq_lineBundle_degree_det {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) :
    VectorBundle.degree E = LineBundle.degree (C := C) (AlgebraicGeometry.VectorBundle.det E) :=
  -- `VectorBundle.degree` is defined as the degree of `det E`; the comparison of the rational-section
  -- and divisor routes is `LineBundle.degree_eq_cartierDivisor_degree`
  rfl

end
