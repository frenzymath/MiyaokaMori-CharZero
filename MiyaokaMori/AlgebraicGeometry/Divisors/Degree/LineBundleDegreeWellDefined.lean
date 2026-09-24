import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.LineBundleIsoLinearEquivalent
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero

/-! # Well-definedness of the degree of a line bundle

`O_C(D) ≅ O_C(D')` implies `deg D = deg D'` (from the vanishing of the degree of a principal divisor
on a smooth projective curve), so the degree of a line bundle is well defined.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem curveDimLeOne {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    topologicalKrullDim C.toScheme ≤ 1 := by
  rw [C.dim_one]

private theorem curveNoetherian {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsNoetherian C.toScheme := by
  haveI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  haveI : CompactSpace C.toScheme :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

private theorem principalWeilCycle_eq_author_generic {k : Type u} [Field k]
    (V : Variety k) (f : V.toScheme.functionFieldˣ)
    [AlgebraicGeometry.IsNoetherian V.toScheme]
    (hdim : topologicalKrullDim V.toScheme ≤ 1) :
    (CartierDivisor.weilCycle V (CartierDivisor.principal f) :
        AlgebraicGeometry.AlgebraicCycle V.toScheme ℤ) =
      ((AlgebraicGeometry.Intersection.principalCartierData f).zeroCycle hdim :
        AlgebraicGeometry.AlgebraicCycle V.toScheme ℤ) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  let D := AlgebraicGeometry.Intersection.principalCartierData f
  have hlocal : CartierDivisor.IsLocalData D.opens
      (fun i => Units.mk0 (D.equation i) (D.equation_ne_zero i)) := by
    dsimp [CartierDivisor.IsLocalData, D]
    constructor
    · ext y
      simp only [AlgebraicGeometry.Intersection.principalCartierData]
      simp
    · intro i j y hy
      constructor
      · refine ⟨1, ?_⟩
        simp [AlgebraicGeometry.Intersection.principalCartierData]
      · refine ⟨1, ?_⟩
        simp [AlgebraicGeometry.Intersection.principalCartierData]
  rw [show CartierDivisor.principal f = CartierDivisor.ofLocalData D.opens
      (fun i => Units.mk0 (D.equation i) (D.equation_ne_zero i)) by rfl]
  let i : D.index := ⟨0⟩
  have hi : x ∈ D.opens i := by
    simp [D, AlgebraicGeometry.Intersection.principalCartierData, i]
  rw [CartierDivisor.weilCycle_ofLocalData V D.opens _ hlocal i x hi]
  rw [AlgebraicGeometry.Intersection.CartierLocalData.zeroCycle_apply]
  simpa [D, AlgebraicGeometry.Intersection.principalCartierData_coefficient] using
    (AlgebraicGeometry.Intersection.CartierLocalData.coefficient_eq_ord_of_mem D x i hi).symm

private theorem principalWeilCycle_eq_author {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (f : C.toScheme.functionFieldˣ)
    (hdim : topologicalKrullDim C.toScheme ≤ 1)
    [AlgebraicGeometry.IsNoetherian C.toScheme] :
    (CartierDivisor.weilCycle C.toVariety (CartierDivisor.principal f) :
        AlgebraicGeometry.AlgebraicCycle C.toScheme ℤ) =
      ((AlgebraicGeometry.Intersection.principalCartierData f).zeroCycle hdim :
        AlgebraicGeometry.AlgebraicCycle C.toScheme ℤ) :=
  principalWeilCycle_eq_author_generic C.toVariety f hdim

private theorem principalWeilCycle_degree_zero {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (f : C.toScheme.functionFieldˣ) :
    CartierDivisor.degree C (CartierDivisor.principal f) = 0 := by
  letI : AlgebraicGeometry.IsNoetherian C.toScheme := curveNoetherian C
  have hdim : topologicalKrullDim C.toScheme ≤ 1 := curveDimLeOne C
  have hproper : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper C.projective
  letI : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hproper
  -- `CartierDivisor.degree` is `AlgebraicCycle.degree (weilCycle D)` and `rawZeroCycleDegree` is an
  -- abbreviation of the same primitive, so `rawZeroCycleDegree_principal_eq_zero` applies by definition
  rw [CartierDivisor.degree_weilCycle, principalWeilCycle_eq_author C f hdim]
  exact AlgebraicGeometry.Intersection.rawZeroCycleDegree_principal_eq_zero
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) hdim f

private theorem degree_add {k : Type u} [Field k] (C : SmoothProjectiveCurve k)
    (D E : CartierDivisor C.toVariety) :
    CartierDivisor.degree C (D + E) = CartierDivisor.degree C D +
      CartierDivisor.degree C E := by
  letI : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper C.projective
  -- the degree is `AlgebraicCycle.degree` of the Weil cycle, so additivity is `degree_add`
  rw [CartierDivisor.degree_weilCycle, CartierDivisor.degree_weilCycle,
    CartierDivisor.degree_weilCycle, CartierDivisor.weilCycle_add]
  exact AlgebraicGeometry.AlgebraicCycle.degree_add _ _

/-- Linearly equivalent divisors (isomorphic line bundles) have the same degree. -/
theorem CartierDivisor.degree_eq_of_lineBundle_iso {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) {D D' : CartierDivisor C.toVariety}
    (e : CartierDivisor.lineBundle D ≅ CartierDivisor.lineBundle D') :
    CartierDivisor.degree C D = CartierDivisor.degree C D' := by
  let eMod : D.lineBundle.toModules ≅ D'.lineBundle.toModules :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := by
        have h := congrArg (fun q => q.hom) e.hom_inv_id
        change e.hom.hom ≫ e.inv.hom = 𝟙 D.lineBundle.toModules at h
        exact h
      inv_hom_id := by
        have h := congrArg (fun q => q.hom) e.inv_hom_id
        change e.inv.hom ≫ e.hom.hom = 𝟙 D'.lineBundle.toModules at h
        exact h }
  obtain ⟨f, hsub⟩ := CartierDivisor.exists_principal_of_lineBundle_iso eMod
  have hrewrite : D = CartierDivisor.principal f + D' := by
    exact sub_eq_iff_eq_add.mp hsub
  rw [hrewrite, degree_add, principalWeilCycle_degree_zero]
  simp

end
