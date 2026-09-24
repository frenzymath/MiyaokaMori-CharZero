import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FlatPullbackCycleMap
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineStalkDvr
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.AffineResidueFieldBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurveIntegral
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02rh
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02rm
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02kb
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOneLemmas
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveProperBirationalModelDominantP1
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.Stacks02ruNormRoute
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PrincipalCartierDivisor

/-! # Principal divisors on a proper curve have degree zero (Stacks 02RU)

On a smooth projective curve a principal divisor has degree zero: `Σ_x ord_x(f) · [κ(x):k] = 0` — the
mathematical content of the well-definedness of the degree of a line bundle.

Source: Stacks 02RU; Hartshorne II, Proposition 6.4(b) (the base case `P¹`); the degree of line bundles on
the curve `C` of Theorem 1.1 of the paper.

The one-dimensional case of Stacks 02RU (on a one-dimensional proper integral scheme over a field `K`,
`Σ_x ord_x(f)·[κ(x):K] = 0`) is stated once in the library, as `principalDivisor_degree_eq_zero` (this
file). The other forms are its corollaries, in the same file:

* `principalDivisor_degree_eq_zero_curve`: the form for a `SmoothProjectiveCurve`;
* `AlgebraicGeometry.Intersection.rawZeroCycleDegree_principal_eq_zero_of_dim_eq_one` /
  `rawZeroCycleDegree_principal_eq_zero`: the encoding through `rawZeroCycleDegree` and
  `principalCartierData`, obtained through the bookkeeping bridge `rawZeroCycleDegree_principal_eq_sum` +
  `Scheme.Hom.residueFieldDegree_eq_residueDegree`.

`ProjectiveLine.sum_ord_mul_residueDegree_eq_zero` (`ProjectiveLinePrincipalDivisorDegreeZero.lean`) is an
**input** of the proof (the base case on `P¹`, Hartshorne II.6.4(b), an elementary computation in `K(t)`);
the theorem is deduced from it by the norm route (`Stacks02ruNormRoute.lean`: 02RT twice + 02R5) for
arbitrary one-dimensional proper varieties.

## Proof (Stacks 02RU, dimension one)

1. View `X` as a `K`-variety `V` (separated and of finite type by properness), `dim V = 1`.
2. `Variety.exists_proper_birational_dominant_projectiveLine` (`CurveProperBirationalModelDominantP1.lean`):
   there are a variety `Y`, a proper birational `p : Y → V` and a proper dominant `q : Y → P¹` (the closure
   of the graph of any nonconstant rational function).
3. `Variety.sum_ord_mul_residueDegree_eq_zero_of_dominant` (`Stacks02ruNormRoute.lean`): pull `f` back to
   `Y` along `p` (birational, degree unchanged), push forward to `P¹` along `q` by the norm (02RT:
   `q_* div(g) = div(Nm g)`), where principal divisors have degree zero
   (`ProjectiveLine.sum_ord_mul_residueDegree_eq_zero`); conclude with 02R5 (pushforward is compatible with
   composition) and the invariance of the degree under pushforward.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 02RU, dimension one** (the only statement of it in the library): on an integral, locally Noetherian
scheme `X`, proper over a field `K` and of dimension one, every unit `f` of the function field has
`Σ_x ord_x(f) · [κ(x) : K] = 0`. Proof: reduce to `P¹` by a proper dominant map from a proper birational model
(`Stacks02ruNormRoute`, 02RT twice + 02R5) and use the elementary computation on `P¹`
(`ProjectiveLine.sum_ord_mul_residueDegree_eq_zero`). -/
theorem principalDivisor_degree_eq_zero {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : SchemeIsOneDimensional X) (f : X.functionFieldˣ) :
    ∑ᶠ x : X, AlgebraicGeometry.Scheme.ord (f : X.functionField) x *
      ((AlgebraicGeometry.Scheme.Hom.residueDegree
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) x : ℕ) : ℤ) = 0 := by
  -- `X` as a `K`-variety `V` (separated and of finite type by properness); `X ↘ Spec K` is `V.toScheme ↘ Spec K`.
  have hsep : AlgebraicGeometry.IsSeparated (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := inferInstance
  have hft : AlgebraicGeometry.IsOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := {}
  let V : Variety K := { carrier := X, separated := hsep, finiteType := hft }
  have : AlgebraicGeometry.IsProper (V.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ‹AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K))›
  have hV : V.toScheme.dimension = 1 := (schemeIsOneDimensional_iff_dim_eq_one V).mp hX
  -- (A′) a proper birational model `Y → V` with a proper dominant map to `P¹`
  obtain ⟨Y, hY, p, _, _, hp, hbir, q, _, _, hq⟩ :=
    V.exists_proper_birational_dominant_projectiveLine hV
  -- the norm route: 02RT twice + 02R5, with (B) the computation on `P¹`
  exact Variety.sum_ord_mul_residueDegree_eq_zero_of_dominant hV hY
    (ProjectiveLine.variety_dimension K) p hp hbir q hq
    (ProjectiveLine.sum_ord_mul_residueDegree_eq_zero K) f

/-- 02RU for a `SmoothProjectiveCurve`. -/
theorem principalDivisor_degree_eq_zero_curve {k : Type u} [Field k] (C : SmoothProjectiveCurve k)
    (f : (C.toScheme.functionField)ˣ) :
    ∑ᶠ x : C.toScheme, AlgebraicGeometry.Scheme.ord (f : C.toScheme.functionField) x *
      ((AlgebraicGeometry.Scheme.Hom.residueDegree (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) x : ℕ) : ℤ) = 0 := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper C.projective
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  exact principalDivisor_degree_eq_zero C.toScheme C.dim_one f

/-! ## 02RU in the `rawZeroCycleDegree` encoding, derived from `principalDivisor_degree_eq_zero`

Users: `CurveModuleDegree.curveModuleDegree_value_unique`, `Divisors/Degree/LineBundleDegreeWellDefined`,
`Chow/Degree/ZeroCycleDegreeScheme`. Both theorems below are bookkeeping bridges: `rawZeroCycleDegree_principal_eq_sum`
writes the degree as a finite sum over the support, `Scheme.Hom.residueFieldDegree_eq_residueDegree` identifies
`residueFieldDegree` with Mathlib's `residueDegree`. Below dimension one every coefficient vanishes
(`principalCartierData_zeroCycle_eq_zero_of_dim_lt_one`).
Sources: Stacks 02RU. -/

namespace AlgebraicGeometry.Intersection

open AlgebraicGeometry Order
open scoped Classical BigOperators

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **Stacks 02RU, dimension-one case, in the `rawZeroCycleDegree` encoding**: `X` integral Noetherian, `c : X → Spec k` proper,
`topologicalKrullDim X = 1`, `a ∈ K(X)ˣ`; then `Σ_x ord_x(a) · [κ(x) : k] = 0`. Derived from
`principalDivisor_degree_eq_zero`; see the module docstring. -/
theorem rawZeroCycleDegree_principal_eq_zero_of_dim_eq_one {k : Type u} [Field k] [IsNoetherian X]
    (c : X ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hdim_one : topologicalKrullDim X = 1) (a : X.functionFieldˣ) :
    rawZeroCycleDegree c ((principalCartierData a).zeroCycle hdim_one.le) = 0 := by
  -- make `X` a `k`-scheme with structure morphism `c`, so that `X ↘ Spec k` is `c` definitionally
  let _ : X.Over (Spec (CommRingCat.of k)) := ⟨c⟩
  have _ : IsProper (X ↘ Spec (CommRingCat.of k)) := ‹IsProper c›
  have h := principalDivisor_degree_eq_zero (K := k) X hdim_one a
  rw [rawZeroCycleDegree_principal_eq_sum, ← h]
  symm
  rw [finsum_eq_sum_of_support_subset]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← Scheme.Hom.residueFieldDegree_eq_residueDegree]
    rfl
  · intro x hx
    rw [Set.Finite.coe_toFinset]
    intro h0
    apply hx
    simp [h0]

/-- A principal divisor has degree zero on any proper integral scheme of dimension `≤ 1` over an arbitrary
field, in the `rawZeroCycleDegree` encoding. Below dimension one every coefficient vanishes
(`principalCartierData_zeroCycle_eq_zero_of_dim_lt_one`); in dimension one it is
`rawZeroCycleDegree_principal_eq_zero_of_dim_eq_one`. -/
theorem rawZeroCycleDegree_principal_eq_zero {k : Type u} [Field k] [IsNoetherian X]
    (c : X ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hdim : topologicalKrullDim X ≤ 1) (a : X.functionFieldˣ) :
    rawZeroCycleDegree c ((principalCartierData a).zeroCycle hdim) = 0 := by
  by_cases hlt : topologicalKrullDim X < 1
  · rw [principalCartierData_zeroCycle_eq_zero_of_dim_lt_one hlt, rawZeroCycleDegree_zero]
  · have hdim_one : topologicalKrullDim X = 1 := le_antisymm hdim (le_of_not_gt hlt)
    exact rawZeroCycleDegree_principal_eq_zero_of_dim_eq_one c hdim_one a

end AlgebraicGeometry.Intersection

end
