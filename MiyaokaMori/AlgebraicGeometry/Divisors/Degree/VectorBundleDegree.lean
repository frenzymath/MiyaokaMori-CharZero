import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegreeDef
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree

/-! # The degree of a vector bundle satisfies the degree relation

`VectorBundle.degree E = LineBundle.degree (det E)` (defined in `VectorBundleDegreeDef`) satisfies
the degree relation `AlgebraicGeometry.Intersection.HasCurveModuleDegree` for `Λ^{rank E} E`
(`VectorBundle.degree_spec`), since `(det E).toModules` is by definition
`AlgebraicGeometry.Scheme.Modules.moduleExteriorPower C E.toModules E.rank`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree of `E` satisfies the degree relation for `Λ^{rank E} E` (the degree of the divisor of a
rational section); this is `LineBundle.degree_spec (det E)`. -/
theorem VectorBundle.degree_spec {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) :
    AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (⟨C.toScheme, C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
      (AlgebraicGeometry.Scheme.Modules.moduleExteriorPower C.toScheme E.toModules E.rank) (VectorBundle.degree E) :=
  LineBundle.degree_spec (AlgebraicGeometry.VectorBundle.det E)

end
