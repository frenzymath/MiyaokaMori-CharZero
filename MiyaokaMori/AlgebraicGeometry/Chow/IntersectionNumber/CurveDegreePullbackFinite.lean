import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme

/-! # Degree of a pulled-back line bundle along a finite morphism of curves

For a finite `K`-morphism `g : Γ' → Γ` between integral, proper, one-dimensional `K`-schemes (generic point
to generic point) and a line bundle `M` on `Γ`: `deg(g^*M) = [K(Γ'):K(Γ)]·deg M` (`Γ` may be singular).
Used in the paper when taking degrees after the finite base change (Lemma 3.1 and §3).

Route (Fulton):
1. `topSelfIntersection_eq_of_dimension_eq_one`: in dimension one the top self-intersection is
   `deg(c_1(L) ∩ [X]_1)` (unfold `capPow` once);
2. the degree is compatible with proper pushforward, `degreeOver_chowPushforward` (`g` finite ⇒ proper,
   Mathlib instance);
3. the projection formula `chowPushforward_firstChernClass_pullback` (`d = 0`);
4. `properPushforward_fundamentalCycle_of_dimension_eq_one`: `g_*[Γ'] = functionFieldDegree g · [Γ]`,
   computing `AlgebraicCycle.map` pointwise: `[Γ']` is `1` only at `η'`
   (`fundamentalCycle_of_isIntegral_of_isOfFiniteType`), both generic points have height `1` (read off
   from the fundamental cycle lying in `Z_1`), so `mapCoeff` at `η'` is `g.residueDegree η'`
   `= functionFieldDegree g` (by definition);
5. `c_1` and `deg` are additive homomorphisms; pull out the coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.CurveDegreePullbackFinite

open AlgebraicGeometry

/-- On a one-dimensional `K`-proper scheme `X`: the top self-intersection `(L^1) = deg(c_1(L) ∩ [X]_1)`
(`capPow` unfolded once at `d = 1`). -/
theorem topSelfIntersection_eq_of_dimension_eq_one {k : Type u} [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (h1 : X.dimension = 1) (L : X.Modules) [L.IsLineBundle] :
    haveI : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
    haveI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
    topSelfIntersection X hX L =
      ChowGroup.degreeOver k X hX (firstChernClass L 1 (X.fundamentalChowClass 1)) := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  unfold topSelfIntersection
  have key : ∀ (d : ℕ), d = 1 →
      ChowGroup.degreeOver k X hX
        (firstChernClass.capPow L d 0
          (cast (congrArg (ChowGroup X) (zero_add d).symm) (X.fundamentalChowClass d))) =
      ChowGroup.degreeOver k X hX (firstChernClass L 1 (X.fundamentalChowClass 1)) := by
    rintro d rfl
    rfl
  exact key _ h1

open Classical in
/-- The fundamental cycle `[X]_1` of a one-dimensional integral `K`-proper scheme is `1` at the generic
point and `0` elsewhere. -/
theorem fundamentalCycle_one_apply {k : Type u} [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    [IsIntegral X] (h1 : X.dimension = 1) :
    haveI : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
    haveI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
    ⇑(X.fundamentalCycle 1) = fun x => if x = genericPoint X then 1 else 0 := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  have : IsOfFiniteType (X ↘ Spec (CommRingCat.of k)) := {}
  have h := X.fundamentalCycle_of_isIntegral_of_isOfFiniteType (k := k)
  rw [h1] at h
  exact h

/-- The generic point of a one-dimensional integral `K`-proper scheme has height `1` (read off from
`[X]_1 ∈ Z_1(X)` and `[X]_1(η) = 1 ≠ 0`). -/
theorem height_genericPoint_eq_one {k : Type u} [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    [IsIntegral X] (h1 : X.dimension = 1) :
    Order.height (genericPoint X) = (1 : ℕ∞) := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  have hmem : X.fundamentalCycle 1 ∈ cycleSubgroup X 1 :=
    (mem_cycleSubgroup_iff_pointClosureDimension _).mpr fun x hx => by
      by_contra h
      exact hx (if_neg h)
  apply hmem (genericPoint X)
  rw [fundamentalCycle_one_apply X hX h1]
  simp

open Classical in
/-- At the level of cycles: `g_*[Γ']_1 = functionFieldDegree g · [Γ]_1`. -/
theorem properPushforward_fundamentalCycle_of_dimension_eq_one {K : Type u} [Field K]
    {Γ' Γ : Scheme.{u}}
    [Γ'.Over (Spec (CommRingCat.of K))] [Γ.Over (Spec (CommRingCat.of K))]
    [IsIntegral Γ'] [IsIntegral Γ]
    (hΓ' : IsProperOver K Γ') (hΓ : IsProperOver K Γ)
    (h1' : Γ'.dimension = 1) (h1 : Γ.dimension = 1)
    (g : Γ' ⟶ Γ) [IsProper g]
    (hg : g.base (genericPoint Γ') = genericPoint Γ) :
    haveI : IsProper (Γ' ↘ Spec (CommRingCat.of K)) := hΓ'
    haveI : IsProper (Γ ↘ Spec (CommRingCat.of K)) := hΓ
    haveI : IsLocallyNoetherian Γ' :=
      LocallyOfFiniteType.isLocallyNoetherian (Γ' ↘ Spec (CommRingCat.of K))
    haveI : IsLocallyNoetherian Γ :=
      LocallyOfFiniteType.isLocallyNoetherian (Γ ↘ Spec (CommRingCat.of K))
    AlgebraicGeometry.AlgebraicCycle.properPushforward g (Γ'.fundamentalCycle 1) =
      (functionFieldDegree g) • Γ.fundamentalCycle 1 := by
  have : IsProper (Γ' ↘ Spec (CommRingCat.of K)) := hΓ'
  have : IsProper (Γ ↘ Spec (CommRingCat.of K)) := hΓ
  have : IsLocallyNoetherian Γ' :=
    LocallyOfFiniteType.isLocallyNoetherian (Γ' ↘ Spec (CommRingCat.of K))
  have : IsLocallyNoetherian Γ :=
    LocallyOfFiniteType.isLocallyNoetherian (Γ ↘ Spec (CommRingCat.of K))
  have hF' := fundamentalCycle_one_apply Γ' hΓ' h1'
  have hF := fundamentalCycle_one_apply Γ hΓ h1
  have hη' := height_genericPoint_eq_one Γ' hΓ' h1'
  have hη := height_genericPoint_eq_one Γ hΓ h1
  -- coefficient: `mapCoeff` at `η'` = `residueDegree` = `functionFieldDegree`
  have hcoeff : AlgebraicCycle.mapCoeff g Order.height Order.height (genericPoint Γ') =
      functionFieldDegree g := by
    unfold AlgebraicCycle.mapCoeff functionFieldDegree
    rw [hg, hη', hη, if_pos rfl]
  ext y
  change (AlgebraicCycle.map g Order.height Order.height (Γ'.fundamentalCycle 1)) y = _
  rw [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
    Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, hF', hF]
  simp only []
  -- the summand is nonzero only at `η'`
  have hsupp : Function.support
      (fun x : Γ' => (if x = genericPoint Γ' then (1 : ℤ) else 0) *
        ((AlgebraicCycle.mapCoeff g Order.height Order.height x : ℕ) : ℤ)) ⊆
        {genericPoint Γ'} := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [Set.mem_singleton_iff]
    by_contra hne
    exact hx (by rw [if_neg hne, zero_mul])
  by_cases hy : y = genericPoint Γ
  · subst hy
    refine (finsum_mem_inter_support_eq' _ _ {genericPoint Γ'} ?_).trans ?_
    · intro x hx
      have hx' : x = genericPoint Γ' := hsupp hx
      subst hx'
      simp [hg]
    · rw [finsum_mem_singleton, if_pos rfl, if_pos rfl, hcoeff]
      simp
  · rw [if_neg hy, smul_zero]
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro x hx
    have hxne : x ≠ genericPoint Γ' := by
      rintro rfl
      have hx2 : g.base (genericPoint Γ') = y := hx
      rw [hg] at hx2
      exact hy hx2.symm
    rw [if_neg hxne, zero_mul]

/-- In the Chow group: `g_*[Γ'] = functionFieldDegree g · [Γ]` (in `A_1`). -/
theorem chowPushforward_fundamentalChowClass_of_dimension_eq_one {K : Type u} [Field K]
    {Γ' Γ : Scheme.{u}}
    [Γ'.Over (Spec (CommRingCat.of K))] [Γ.Over (Spec (CommRingCat.of K))]
    [IsIntegral Γ'] [IsIntegral Γ]
    (hΓ' : IsProperOver K Γ') (hΓ : IsProperOver K Γ)
    (h1' : Γ'.dimension = 1) (h1 : Γ.dimension = 1)
    (g : Γ' ⟶ Γ) [g.IsOver (Spec (CommRingCat.of K))] [IsProper g]
    (hg : g.base (genericPoint Γ') = genericPoint Γ) :
    haveI : IsProper (Γ' ↘ Spec (CommRingCat.of K)) := hΓ'
    haveI : IsProper (Γ ↘ Spec (CommRingCat.of K)) := hΓ
    haveI : IsLocallyNoetherian Γ' :=
      LocallyOfFiniteType.isLocallyNoetherian (Γ' ↘ Spec (CommRingCat.of K))
    haveI : IsLocallyNoetherian Γ :=
      LocallyOfFiniteType.isLocallyNoetherian (Γ ↘ Spec (CommRingCat.of K))
    chowPushforward g 1 (Γ'.fundamentalChowClass 1) =
      (functionFieldDegree g) • Γ.fundamentalChowClass 1 := by
  have : IsProper (Γ' ↘ Spec (CommRingCat.of K)) := hΓ'
  have : IsProper (Γ ↘ Spec (CommRingCat.of K)) := hΓ
  have : IsLocallyNoetherian Γ' :=
    LocallyOfFiniteType.isLocallyNoetherian (Γ' ↘ Spec (CommRingCat.of K))
  have : IsLocallyNoetherian Γ :=
    LocallyOfFiniteType.isLocallyNoetherian (Γ ↘ Spec (CommRingCat.of K))
  have hdesc : PushforwardDescends g 1 :=
    AlgebraicCycle.properPushforward_rationallyEquivalent (k := K) g 1
  unfold Scheme.fundamentalChowClass
  rw [chowPushforward_mk g 1 hdesc, ← map_nsmul]
  congr 1
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul]
  exact properPushforward_fundamentalCycle_of_dimension_eq_one hΓ' hΓ h1' h1 g hg

end MiyaokaMori.CurveDegreePullbackFinite

theorem AlgebraicGeometry.topSelfIntersection_pullback_of_finite {K : Type u} [Field K]
    {Γ' Γ : AlgebraicGeometry.Scheme.{u}}
    [Γ'.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] [Γ.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Γ'] [AlgebraicGeometry.IsIntegral Γ]
    (hΓ' : IsProperOver K Γ') (hΓ : IsProperOver K Γ)
    (h1' : Γ'.dimension = 1) (h1 : Γ.dimension = 1)
    (g : Γ' ⟶ Γ) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsFinite g]
    (hg : g.base (genericPoint Γ') = genericPoint Γ)
    (M : Γ.Modules) [M.IsLineBundle]
    [((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).IsLineBundle] :
    AlgebraicGeometry.topSelfIntersection Γ' hΓ' ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
      = (functionFieldDegree g : ℤ) * AlgebraicGeometry.topSelfIntersection Γ hΓ M := by
  have : IsProper (Γ' ↘ Spec (CommRingCat.of K)) := hΓ'
  have : IsProper (Γ ↘ Spec (CommRingCat.of K)) := hΓ
  have : IsLocallyNoetherian Γ' :=
    LocallyOfFiniteType.isLocallyNoetherian (Γ' ↘ Spec (CommRingCat.of K))
  have : IsLocallyNoetherian Γ :=
    LocallyOfFiniteType.isLocallyNoetherian (Γ ↘ Spec (CommRingCat.of K))
  rw [MiyaokaMori.CurveDegreePullbackFinite.topSelfIntersection_eq_of_dimension_eq_one Γ' hΓ' h1',
    MiyaokaMori.CurveDegreePullbackFinite.topSelfIntersection_eq_of_dimension_eq_one Γ hΓ h1]
  -- the degree is compatible with the pushforward
  rw [← MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward hΓ' hΓ g]
  -- projection formula (`d = 0`; `0 + 1` and `1` are definitionally equal)
  have hproj : chowPushforward g 0
      (firstChernClass ((Scheme.Modules.pullback g).obj M) 1 (Γ'.fundamentalChowClass 1)) =
      firstChernClass M 1 (chowPushforward g 1 (Γ'.fundamentalChowClass 1)) :=
    chowPushforward_firstChernClass_pullback (k := K) g M 0 (Γ'.fundamentalChowClass 1)
  rw [hproj,
    MiyaokaMori.CurveDegreePullbackFinite.chowPushforward_fundamentalChowClass_of_dimension_eq_one
      hΓ' hΓ h1' h1 g hg,
    map_nsmul, map_nsmul, nsmul_eq_mul]

end
