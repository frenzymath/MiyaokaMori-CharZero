import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeDef
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveModuleDegreeDifferenceOfEffective
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.EulerCharEffectiveCartierTwist
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.LineBundleDifferenceOfEffective

/-! # The degree of a line bundle on a curve and the top self-intersection

The degree `LineBundle.degree` of a line bundle on a smooth projective curve (defined in
`LineBundleDegreeDef` as `deg L := χ(C, L) − χ(C, O_C)`, Stacks 0AYR) equals the top
self-intersection `topSelfIntersection C.toScheme hC L.toModules = deg(c₁(L) ∩ [C])` of the Chow
route (`LineBundle.degree_eq_topSelfIntersection`). Consequently it satisfies the degree relation
`AlgebraicGeometry.Intersection.HasCurveModuleDegree` (the degree of the zero cycle of a nonzero rational
section; `LineBundle.degree_spec`), equals any value satisfying that relation, and is invariant
under isomorphism.

Proof of the bridge (Riemann–Roch route, Stacks 0AZ3, 0AYY, 0AYR): write `L ≅ O(A) ⊗ O(B)^∨` with
`A`, `B` effective Cartier divisors (`exists_effectiveCartierDivisor_sub`); then
`χ(L) = χ(O(A)) − deg_k B` and `χ(O(A)) = χ(O_C) + deg_k A`, while
`topSelfIntersection L = deg_k A − deg_k B` (`topSelfIntersection_of_iso_tensor_dual_effectiveCartier`).
Downstream code should use `LineBundle.degree` only through these theorems, not by unfolding the
definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The bridge: `deg L` (difference of Euler characteristics) equals the top self-intersection
`deg(c₁(L) ∩ [C])`. Riemann–Roch route, see the module docstring. -/
theorem LineBundle.degree_eq_topSelfIntersection {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (hC : IsProperOver k C.toScheme)
    (L : LineBundle C.toVariety) :
    L.degree = AlgebraicGeometry.topSelfIntersection C.toScheme hC L.toModules := by
  have : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  have : AlgebraicGeometry.IsNoetherian C.toScheme :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hdim : C.toScheme.dimension = 1 :=
    MiyaokaMori.TopSelfIntersectionCurve.dimension_eq_one_of_schemeIsOneDimensional C.dim_one
  obtain ⟨A, B, ⟨e⟩⟩ := AlgebraicGeometry.exists_effectiveCartierDivisor_sub C.toScheme
    C.projective L.toModules
  have h1 := AlgebraicGeometry.sheafEulerCharacteristic_of_iso_tensor_dual_effectiveCartier
    (k := k) hC C.dim_one B A.lineBundle _ e
  have h2 := AlgebraicGeometry.sheafEulerCharacteristic_effectiveCartier_lineBundle
    (k := k) hC C.dim_one A
  have h3 := AlgebraicGeometry.topSelfIntersection_of_iso_tensor_dual_effectiveCartier
    (k := k) hC hdim A B _ e
  rw [LineBundle.degree_def, h1, h2, h3]
  ring

/-- The degree satisfies the degree relation `HasCurveModuleDegree` (through the bridge and
`hasCurveModuleDegree_topSelfIntersection`). -/
theorem LineBundle.degree_spec {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (⟨C.toScheme, C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
      L.toModules (LineBundle.degree L) := by
  have : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  rw [LineBundle.degree_eq_topSelfIntersection C C.isProper L]
  exact MiyaokaMori.TopSelfIntersectionCurve.hasCurveModuleDegree_topSelfIntersection C.isProper
    (MiyaokaMori.TopSelfIntersectionCurve.dimension_eq_one_of_schemeIsOneDimensional C.dim_one)
    L.toModules

/-- Any value satisfying the degree relation is the degree
(`hasCurveModuleDegree_iff_eq_topSelfIntersection`; uniqueness comes from the vanishing of the degree
of a principal divisor on a proper integral curve). -/
theorem LineBundle.degree_eq_of_hasCurveModuleDegree {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) {d : ℤ}
    (hd : AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (⟨C.toScheme, C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
      L.toModules d) :
    LineBundle.degree L = d := by
  have : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  rw [LineBundle.degree_eq_topSelfIntersection C C.isProper L]
  exact ((MiyaokaMori.TopSelfIntersectionCurve.hasCurveModuleDegree_iff_eq_topSelfIntersection
    C.isProper (MiyaokaMori.TopSelfIntersectionCurve.dimension_eq_one_of_schemeIsOneDimensional C.dim_one)
    L.toModules d).mp hd).symm

/-- Isomorphic line bundles have the same degree (for an isomorphism of the underlying modules; an
isomorphism `e : L ≅ M` of line bundles is converted by `modulesIsoOfLineBundleIso e`): the top
self-intersection depends only on the isomorphism class (`topSelfIntersection_congr`). -/
theorem LineBundle.degree_congr {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {L M : LineBundle C.toVariety} (e : L.toModules ≅ M.toModules) :
    LineBundle.degree L = LineBundle.degree M := by
  rw [LineBundle.degree_eq_topSelfIntersection C C.isProper L,
    LineBundle.degree_eq_topSelfIntersection C C.isProper M]
  exact AlgebraicGeometry.topSelfIntersection_congr C.toScheme C.isProper _ _ e

end
