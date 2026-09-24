import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveModuleDegree

/-! # Degree of a line bundle on an integral curve

The degree `deg(L|_Γ) := (ι^*L)^1 = deg(c_1(ι^*L) ∩ [Γ])` of a line bundle on an integral curve `Γ` in
an arbitrary `k`-scheme `X` (`Γ` integral, proper over `k`, one-dimensional; neither `X` nor `Γ` need be
smooth). This is `topSelfIntersection` in the one-dimensional case, used uniformly in the positivity
arguments on `Y_k^GG` (Lemma 2.5 of the paper).

The definition body is literally
`Γ.degree L := topSelfIntersection Γ.carrier Γ.isProperOver (ι^*L) = degreeOver k Γ (c₁(ι^*L) ∩ [Γ])`,
the scheme-level 0-cycle degree of the first Chern class capped with the fundamental class (Fulton,
*Intersection Theory*, Ex. 2.5.1 / Stacks 02SV). The relation `HasCurveModuleDegree` (degree of the divisor
of a rational section) is a *theorem* about this value (`IntegralCurve.degree_spec`), not part of the
definition. Fallbacks inherited from the primitive: `ChowGroup.degreeOver` is a `finsum` (`0` on infinite
support — impossible here, `Γ` is proper over `k`) and `firstChernClass` is the `0` map when Stacks 02TI
fails (`hasCurveModuleDegree_topSelfIntersection` proves the value equals `deg div(s)` for a rational
section `s`, so that branch never fires on a proper integral curve). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree `deg(L|_Γ) = (ι^*L)^1 = deg_k(c₁(ι^*L) ∩ [Γ])`: `topSelfIntersection` on the one-dimensional
integral proper `k`-scheme `Γ.carrier`, applied to the pullback `ι^*L`. -/
noncomputable def IntegralCurve.degree {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X)
    (L : X.Modules) [L.IsLineBundle] : ℤ :=
  AlgebraicGeometry.topSelfIntersection Γ.carrier Γ.isProperOver
    ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L)

/-- Unfolding of the definition (`rfl`), for users that need the Chow-side shape. -/
theorem IntegralCurve.degree_eq_topSelfIntersection {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X)
    (L : X.Modules) [L.IsLineBundle] :
    Γ.degree L = AlgebraicGeometry.topSelfIntersection Γ.carrier Γ.isProperOver
      ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L) := rfl

/-- The degree satisfies the relation `HasCurveModuleDegree` (degree of the divisor of a rational
section): the one-dimensional case of `hasCurveModuleDegree_topSelfIntersection`; the `k`-structure
morphism of `Γ.carrier` is `Γ.ι ≫ (X ↘ Spec k)`, which is definitionally that of
`closedCurveOver ⟨X, X ↘ Spec k⟩ Γ.ι`. -/
theorem IntegralCurve.degree_spec {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X)
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (AlgebraicGeometry.Intersection.closedCurveOver
        (⟨X, X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k) Γ.ι)
      ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L) (Γ.degree L) :=
  MiyaokaMori.TopSelfIntersectionCurve.hasCurveModuleDegree_topSelfIntersection
    (k := k) (X := Γ.carrier) Γ.isProperOver Γ.carrier_dimension
    ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L)

/-- Uniqueness: any `d` satisfying the relation `HasCurveModuleDegree` equals `Γ.degree L`
(`hasCurveModuleDegree_iff_eq_topSelfIntersection`). -/
theorem IntegralCurve.degree_eq_of_hasCurveModuleDegree {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X)
    (L : X.Modules) [L.IsLineBundle] {d : ℤ}
    (hd : AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (AlgebraicGeometry.Intersection.closedCurveOver
        (⟨X, X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k) Γ.ι)
      ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L) d) :
    Γ.degree L = d :=
  ((MiyaokaMori.TopSelfIntersectionCurve.hasCurveModuleDegree_iff_eq_topSelfIntersection
    (k := k) (X := Γ.carrier) Γ.isProperOver Γ.carrier_dimension
    ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L) d).mp hd).symm

/-- `deg(L|_Γ) = deg_k div_{ι^*L}(s)` for any nonzero rational section `s` of `ι^*L` (Stacks 0BEY;
`topSelfIntersection_eq_degree_rationalSectionDivisor` on `Γ.carrier`). -/
theorem IntegralCurve.degree_eq_degree_rationalSectionDivisor {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Γ : IntegralCurve k X) (L : X.Modules) [L.IsLineBundle]
    [AlgebraicGeometry.IsLocallyNoetherian Γ.carrier]
    (s : ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L).stalk (genericPoint Γ.carrier))
    (hs : s ≠ 0) :
    Γ.degree L = AlgebraicGeometry.AlgebraicCycle.degree (k := k)
      (((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L).rationalSectionDivisor s) :=
  MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_degree_rationalSectionDivisor
    (k := k) (X := Γ.carrier) Γ.isProperOver Γ.carrier_dimension
    ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L) s hs

/-- `deg(L|_Γ)` depends only on the isomorphism class of `ι^*L` (`topSelfIntersection_congr`). -/
theorem IntegralCurve.degree_congr {K : Type u} [Field K] {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (Γ : IntegralCurve K Y)
    {L L' : Y.Modules} [L.IsLineBundle] [L'.IsLineBundle]
    (e : (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L ≅
      (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L') :
    Γ.degree L = Γ.degree L' :=
  AlgebraicGeometry.topSelfIntersection_congr Γ.carrier Γ.isProperOver _ _ e

end
