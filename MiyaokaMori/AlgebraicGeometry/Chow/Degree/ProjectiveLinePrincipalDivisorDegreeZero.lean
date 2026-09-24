import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOneLemmas
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ProjectiveLineChartsPrincipalDivisorDegree

/-! # Principal divisors on the projective line have degree zero

Every nonzero rational function on `P¹_K` has a principal divisor of degree zero:
`Σ_y ord_y(h)·[κ(y):K] = 0` (`K` an arbitrary field); also `P¹` as a `K`-variety,
`ProjectiveLine.variety`.

The proof is split into two modules:
* `AffineLinePrincipalDivisorDegree.lean`: the computation on the affine line `Spec K[X]` — `ord_{(π)} π = 1`,
  `f ∉ q ⇒ ord_q f = 0`, `[κ((π)):K] = deg π`, `Σ_q ord_q(f)·[κ(q):K] = deg f` (by induction on the prime
  factorization of `f`), and the computation at `∞`, `ord_{(X)}(reverse f / X^{deg f}) = −deg f`.
* `ProjectiveLineChartsPrincipalDivisorDegree.lean`: the two standard charts `chartι K i : Spec K[X] → P¹`
  (`X ↦ x_j/x_i`), the decomposition of points `P¹ = D₊(x₀) ⊔ {∞}`, transport of rational functions along
  the charts, the transition between the charts (`(x₁/x₀)(x₀/x₁) = 1`, constants agree) and the final
  assembly `sum_ord_mul_residueDegree_eq_zero_proj` (stated for Mathlib's
  `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)`, which is definitionally
  `(ProjectiveLine.variety K).toScheme`, so the theorem of this file follows by `exact`).

Source: Hartshorne II, Proposition 6.4(b) (`n = 1`).
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

variable (K : Type u) [Field K]

/-- `P¹` as a variety over `K`. An opaque `def` (not an `abbrev`), so that the statements below do not
contain two spellings of the same object. -/
def ProjectiveLine.variety : Variety K :=
  (ProjectiveLine.asSmoothProjectiveCurve K).toVariety

instance ProjectiveLine.variety_isProper :
    IsProper ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K)) :=
  SmoothProjectiveCurve.isProper (ProjectiveLine.asSmoothProjectiveCurve K)

theorem ProjectiveLine.variety_dimension : (ProjectiveLine.variety K).toScheme.dimension = 1 :=
  (schemeIsOneDimensional_iff_dim_eq_one (ProjectiveLine.variety K)).mp
    (ProjectiveLine.asSmoothProjectiveCurve K).dim_one

/-- **The principal divisor of any rational function on `P¹` has degree zero.**
Route: `K(P¹) ≅ K(t)`; `h = a/b` (`a, b ∈ K[t]`, transported through the chart `D₊(x₀) = Spec K[t]`,
`ProjectiveLine.chartSectionHom`); at the finite points `Σ_q ord_q(a)·[κ(q):K] = deg a`
(`affineLine_finsum_ord_mul_residueDegree`), at `∞ = [0:1]` one has `ord_∞(a) = −deg a` with residue degree
`1` (second chart and transition `t ↦ 1/t`: `a(t) = reverse(a)(1/t)·t^{deg a}`); the two parts cancel.
`(ProjectiveLine.variety K).toScheme` is definitionally Mathlib's `Proj (homogeneousSubmodule (Fin 2) K)`,
so the theorem follows from `ProjectiveLine.sum_ord_mul_residueDegree_eq_zero_proj`. -/
theorem ProjectiveLine.sum_ord_mul_residueDegree_eq_zero
    (h : (ProjectiveLine.variety K).toScheme.functionFieldˣ) :
    ∑ᶠ y : (ProjectiveLine.variety K).toScheme,
      Scheme.ord (h : (ProjectiveLine.variety K).toScheme.functionField) y *
        ((Scheme.Hom.residueDegree
          ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) = 0 :=
  ProjectiveLine.sum_ord_mul_residueDegree_eq_zero_proj K h

end
