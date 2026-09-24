import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.AffineResidueFieldBase
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero

/-! # The degree of zero-cycles on a proper scheme over a field

The degree `deg(Σ n_p[p]) = Σ n_p·[κ(p):k]` of zero-cycles on a scheme `X` proper over `k`, descended to
an additive homomorphism `deg : A_0(X) → ℤ` on the Chow group (rationally equivalent zero-cycles have the
same degree; the integer version of Fulton Def. 1.4 / Stacks 0AZ1). `ChowGroup.degree` on smooth projective
varieties over an algebraically closed field is a special case, and the ℚ-valued degree
`ChowGroupRat.degree` is the ℚ-extension. `ChowGroup.degreeOver` is obtained from `AlgebraicCycle.degree`
by descent through the quotient map (properness of `X` is needed for the invariance under rational
equivalence). Used for the fiber degree (2.6) of the paper. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree `deg : A_0(X) → ℤ` on the Chow group of a scheme `X` proper over `k`: the descent of
`AlgebraicCycle.degree` (`∑ᶠ x, Z x · [κ(x):k]`, defined in `ZeroCycleDegree.lean`) to rational
equivalence classes. -/
noncomputable def AlgebraicGeometry.ChowGroup.degreeOver (k : Type u) [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) : AlgebraicGeometry.ChowGroup X 0 →+ ℤ :=
  let φ : ↥(AlgebraicGeometry.cycleSubgroup X 0) →+ ℤ :=
    AddMonoidHom.mk'
      (fun Z : ↥(AlgebraicGeometry.cycleSubgroup X 0) =>
        AlgebraicGeometry.AlgebraicCycle.degree (k := k)
          (Z : AlgebraicGeometry.AlgebraicCycle X ℤ))
      (by
        intro Z W
        letI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
        exact AlgebraicGeometry.AlgebraicCycle.degree_add (k := k)
          (Z : AlgebraicGeometry.AlgebraicCycle X ℤ) (W : AlgebraicGeometry.AlgebraicCycle X ℤ))
  QuotientAddGroup.lift _ φ (by
    intro c hc
    change AlgebraicGeometry.AlgebraicCycle.degree (k := k)
      (c : AlgebraicGeometry.AlgebraicCycle X ℤ) = 0
    have hc' : (c : AlgebraicGeometry.AlgebraicCycle X ℤ) ∈
        AlgebraicGeometry.ratEquivZero X 0 := hc
    have hdeg : ∀ z : AlgebraicGeometry.AlgebraicCycle X ℤ,
        z ∈ AlgebraicGeometry.ratEquivZero X 0 →
          AlgebraicGeometry.AlgebraicCycle.degree (k := k) z = 0 := by
      intro z hz
      -- `ratEquivZero` is the locally finite sum of Stacks 02RW; since `X` is proper over a field it is
      -- Noetherian (in particular quasi-compact), so locally finite families are finite and
      -- `ratEquivZero_eq_finite_of_compactSpace` gives the finitely generated form, on which the
      -- induction over generators runs
      letI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
      letI : AlgebraicGeometry.IsNoetherian X :=
        AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      rw [AlgebraicGeometry.ratEquivZero_eq_finite_of_compactSpace,
        AlgebraicGeometry.ratEquivZeroFinite] at hz
      induction hz using AddSubgroup.closure_induction with
      | mem c hc =>
        obtain ⟨w, hw, hwi, hwiι, hwN, f, rfl⟩ := hc
        let W := AlgebraicGeometry.Scheme.pointClosure w
        let i := AlgebraicGeometry.Scheme.pointClosureι w
        let p := X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
        let q := i ≫ p
        letI : AlgebraicGeometry.IsIntegral W := hwi
        letI : AlgebraicGeometry.IsClosedImmersion i := hwiι
        letI : AlgebraicGeometry.IsLocallyNoetherian W := hwN
        letI : AlgebraicGeometry.IsProper p := hX
        letI : AlgebraicGeometry.IsProper i := inferInstance
        letI : AlgebraicGeometry.IsProper q := inferInstance
        -- the generators of `ratEquivZero` do not carry `CompactSpace W`; here `W` is proper over a
        -- field, so `properFieldScheme_isNoetherian` gives `IsNoetherian W` (including quasi-compactness)
        letI : AlgebraicGeometry.IsNoetherian W :=
          AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian q
        have hdimW : topologicalKrullDim W ≤ 1 := by
          rw [show topologicalKrullDim W =
            AlgebraicGeometry.Intersection.pointClosureDimension X w from
              (AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure X w).symm]
          rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height]
          simpa using hw.le
        have hsrc : AlgebraicGeometry.Intersection.IsDimensionCycle W 0
            (W.principalCycle f) := by
          rw [AlgebraicGeometry.Scheme.principalCycle_eq_zeroCycle W f hdimW]
          exact ((AlgebraicGeometry.Intersection.principalCartierData f).zeroCycle hdimW).2
        have hpush : AlgebraicGeometry.Intersection.IsDimensionCycle X 0
            (AlgebraicGeometry.AlgebraicCycle.properPushforward i (W.principalCycle f)) :=
          AlgebraicGeometry.AlgebraicCycle.properPushforward_mem_cycleSubgroup_of_mem i 0 hsrc
        let Z : ↥(AlgebraicGeometry.cycleSubgroup X 0) :=
          ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward i (W.principalCycle f), hpush⟩
        -- `rawZeroCycleDegree p Z` is an abbrev of `AlgebraicCycle.degree Z.1` (with the structure
        -- morphism `p` explicit): equal by definition
        change AlgebraicGeometry.Intersection.rawZeroCycleDegree p Z = 0
        have hβ := AlgebraicGeometry.Intersection.rawZeroCycleDegree_closedImmersion
          p i ((AlgebraicGeometry.Intersection.principalCartierData f).zeroCycle hdimW)
        have hdimpush :
            Z =
              AlgebraicGeometry.Intersection.dimensionProperPushforward i 0
                ((AlgebraicGeometry.Intersection.principalCartierData f).zeroCycle hdimW) := by
          apply Subtype.ext
          change AlgebraicGeometry.AlgebraicCycle.properPushforward i (W.principalCycle f) =
            AlgebraicGeometry.AlgebraicCycle.properPushforward i
              ((AlgebraicGeometry.Intersection.principalCartierData f).zeroCycle hdimW).1
          rw [AlgebraicGeometry.Scheme.principalCycle_eq_zeroCycle W f hdimW]
        rw [hdimpush]
        change AlgebraicGeometry.Intersection.rawZeroCycleDegree p
          (AlgebraicGeometry.Intersection.dimensionProperPushforward i 0
            ((AlgebraicGeometry.Intersection.principalCartierData f).zeroCycle hdimW)) = 0
        rw [hβ]
        exact AlgebraicGeometry.Intersection.rawZeroCycleDegree_principal_eq_zero q hdimW f
      | zero =>
        rw [AlgebraicGeometry.AlgebraicCycle.degree_zero]
      | add a b _ _ ha hb =>
        rw [AlgebraicGeometry.AlgebraicCycle.degree_add a b, ha, hb, add_zero]
      | neg a _ ha =>
        rw [AlgebraicGeometry.AlgebraicCycle.degree_neg a, ha, neg_zero]
    exact hdeg (c : AlgebraicGeometry.AlgebraicCycle X ℤ) hc')

end
