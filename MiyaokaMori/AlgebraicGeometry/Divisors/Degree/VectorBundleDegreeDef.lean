import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRankOne
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierPresentationExistence
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DeterminantLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeDef
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # Definition of the degree of a vector bundle on a curve

The degree of a vector bundle on a smooth projective curve, `deg E := deg(det E)` with
`det E = Λ^{rank E} E` (equivalently, the degree of `c_1(E)`); Hartshorne Ex. II.6.12, Stacks 0AZ3.
This is the degree `deg f^*T_X` of Theorem 1.1 of the paper and `deg E = d` in
(2.3).

The characterizing lemma `VectorBundle.degree_spec` is in `VectorBundleDegree`; the definition is kept
in this separate module so that modules using only the definition (such as `TangentBundlePullback`)
can import it without the Riemann–Roch route, avoiding an import cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree of a vector bundle `E` on a smooth projective curve: `deg E := deg (det E)`. Since
`(det E).toModules` is by definition `AlgebraicGeometry.Scheme.Modules.moduleExteriorPower C E.toModules E.rank`,
`VectorBundle.degree_eq_lineBundle_degree_det` is `rfl` and `VectorBundle.degree_spec` follows from
`LineBundle.degree_spec (det E)`. -/
noncomputable def VectorBundle.degree {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) : ℤ :=
  LineBundle.degree (AlgebraicGeometry.VectorBundle.det E)

end
