import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # Degree of a relative polarization on a fiber

The degree `v = (L|_{X_c})^{dim X_c}` of a relative polarization on a fiber (the fiber degree
(2.6) of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree `(L|_{Y_c})^{dim Y_c}` of a relative polarization `L` on the fiber `Y_c` of `f : Y → X` over
`c`, viewed as a scheme over `κ(c)`. -/
noncomputable def AlgebraicGeometry.relativePolarizationFiberDegree
    {Y X : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) (L : Y.Modules) [L.IsLineBundle]
    (c : X) (hf : letI := f.fiberOverSpecResidueField c; IsProperOver (X.residueField c) (f.fiber c)) :
    ℤ :=
  letI := f.fiberOverSpecResidueField c
  AlgebraicGeometry.topSelfIntersection (f.fiber c) hf
    ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι c)).obj L)

end
