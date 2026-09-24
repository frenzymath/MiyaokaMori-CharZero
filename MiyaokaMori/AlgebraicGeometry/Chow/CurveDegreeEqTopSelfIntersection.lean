import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.LineBundleIsDivisorial
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve

/-! # The degree of a line bundle on a curve is its top self-intersection

The degree of a line bundle on a smooth projective curve (`LineBundle.degree`, defined through
divisors) equals the top self-intersection `deg(c_1(L) ∩ [C])` of the Chow route (the comparison of
`d_L = deg L` with the intersection number of `τ^*B_k` in §3 of the paper).

The theorem `LineBundle.degree_eq_topSelfIntersection` lives in `LineBundleDegree.lean` (imported
here), where it is the bridge from which `LineBundle.degree_spec` / `degree_congr` are derived. This
module keeps its imports so that downstream import paths are unchanged. -/

set_option autoImplicit false

