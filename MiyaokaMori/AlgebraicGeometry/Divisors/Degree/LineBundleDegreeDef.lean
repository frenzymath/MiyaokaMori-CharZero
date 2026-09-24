import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.LineBundleIsDivisorial
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleLocallyFreeRank
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristicDef
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveModuleDegree

/-! # Definition of the degree of a line bundle on a curve

The degree of a line bundle on a smooth projective curve, following Stacks 0AYR (varieties,
`definition-degree-invertible-sheaf`): `deg L := χ(C, L) − χ(C, O_C)`.

The characterizing lemmas `LineBundle.degree_spec`, `degree_eq_of_hasCurveModuleDegree` and
`degree_congr` are in `LineBundleDegree`; they are proved by the Riemann–Roch route, whose import
closure contains `TangentBundlePullback` (which uses `VectorBundle.degree`), so the definition is
kept in this separate module to avoid an import cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree of a line bundle `L` on a smooth projective curve, `deg L = χ(C, L) − χ(C, O_C)`
(Stacks 0AYR). The definition involves no choice. The two `0` fallbacks of `sheafEulerCharacteristic`
(infinite-dimensional `finrank`, infinite-support `finsum`) are never triggered for a line bundle on a
proper curve (`sheafCohomology_finite_and_vanishing`), and `LineBundle.degree_spec` shows that this
value satisfies the degree relation `HasCurveModuleDegree` (the degree of the divisor of a rational
section), so it is the degree of the literature. -/
noncomputable def LineBundle.degree {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) : ℤ :=
  AlgebraicGeometry.sheafEulerCharacteristic (k := k) C.toScheme L.toModules -
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) C.toScheme
      (SheafOfModules.unit C.toScheme.ringCatSheaf)

/-- The unfolded form of the definition (use this rather than unfolding `LineBundle.degree`). -/
theorem LineBundle.degree_def {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    LineBundle.degree L =
      AlgebraicGeometry.sheafEulerCharacteristic (k := k) C.toScheme L.toModules -
        AlgebraicGeometry.sheafEulerCharacteristic (k := k) C.toScheme
          (SheafOfModules.unit C.toScheme.ringCatSheaf) :=
  rfl

end
