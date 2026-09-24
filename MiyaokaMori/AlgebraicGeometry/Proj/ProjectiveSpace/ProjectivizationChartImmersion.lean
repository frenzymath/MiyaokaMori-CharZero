import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple

/-! # Chart analysis of the projectivization morphism

Chart-by-chart analysis of the projectivization morphism
`φ = projectivizationMorphism M P hP : V → P^N`:
1. `chartEvaluation` (`ProjectiveSpaceOverChart`) is surjective when `e` is surjective and
   `e(x_j) = 1` (`chartEvaluation_surjective`; auxiliary formula `chartEvaluation_mk_mul_pow`).
2. If `V_ℓ` is affine and the chart evaluation `k[x] → Γ(V_ℓ, O)` is surjective, the chart map
   `g_ℓ : V_ℓ → D_+(x_ℓ)` is a closed immersion (`isClosedImmersion_projectivizationChartMap`:
   `g_ℓ = toSpecΓ ≫ Spec.map(chartEvaluation) ≫ basicOpenIsoSpec.inv`, and Mathlib's
   `IsClosedImmersion.spec_of_surjective`).
3. If generators `t_i ∈ Γ(V, V_ℓ)` of `Γ(V_ℓ, O)` are all ratios `P_{j(i)}/P_ℓ`, the chart
   evaluation is surjective (`projectivizationChartEval_surjective_of_generators`).
4. If the charts of a covering index set `S` are closed immersions and the `V_ℓ` (`ℓ ∈ S`) cover
   `V`, then `φ` is an immersion (`isImmersion_projectivizationMorphism_of_charts`: Mathlib's
   `IsZariskiLocalAtTarget.of_range_subset_iSup`, `φ⁻¹D_+(x_ℓ) = V_ℓ` by
   `projectivizationMorphism_preimage_basicOpen`, and `φ ∣_ D_+(x_ℓ) = isoOfEq ≫ g_ℓ` by the
   general lemma `morphismRestrict_eq_isoOfEq_comp`).

Reference: Stacks 01VU, third paragraph of the proof (Spec of a surjection is a closed
immersion; glue over the `D_+(x_ℓ)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-! The three theorems below are the `R := k` instances of
`isClosedImmersion_projectivizationChartMapOver`, `isImmersion_projectivizationMorphismOver_of_charts`
and `projectivizationChartEvalOver_surjective_of_generators` (`ProjectivizationOverRing.lean`); the
field-level names are `abbrev`s of the over-ring ones, so the statements are the same terms. -/

/-- **Closed immersion of a chart map**: if the chart `V_ℓ` is affine and the chart evaluation
`k[x_0,…,x_N] → Γ(V_ℓ, O)` is surjective, then `g_ℓ : V_ℓ → D_+(x_ℓ)` is a closed immersion. -/
theorem isClosedImmersion_projectivizationChartMap {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1))
    (haff : AlgebraicGeometry.IsAffineOpen (projectivizationChart P ℓ))
    (hsurj : Function.Surjective (projectivizationChartEval (k := k) P ℓ)) :
    AlgebraicGeometry.IsClosedImmersion (projectivizationChartMap (k := k) P ℓ) :=
  isClosedImmersion_projectivizationChartMapOver _ P ℓ haff hsurj

/-- **Immersion criterion for the projectivization morphism**: if the charts `V_ℓ`, `ℓ ∈ S`, cover
`V` and each chart map `g_ℓ : V_ℓ → D_+(x_ℓ)` (`ℓ ∈ S`) is a closed immersion, then the glued
morphism `φ : V → P^N` is an immersion (`IsZariskiLocalAtTarget.of_range_subset_iSup`: `φ` lands in
`U = ⋃_{ℓ ∈ S} D_+(x_ℓ)` and `φ ∣_ D_+(x_ℓ) ≅ g_ℓ`). -/
theorem isImmersion_projectivizationMorphism_of_charts {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (S : Set (Fin (N + 1)))
    (hcov : ∀ v : V, ∃ ℓ ∈ S, ¬ IsZeroAt (P ℓ) v)
    (hcl : ∀ ℓ ∈ S, AlgebraicGeometry.IsClosedImmersion (projectivizationChartMap (k := k) P ℓ)) :
    AlgebraicGeometry.IsImmersion (projectivizationMorphism (k := k) M P hP) :=
  isImmersion_projectivizationMorphismOver_of_charts _ M P hP S hcov hcl

/-- **Surjectivity of the chart evaluation from generators**: if the chart `V_ℓ = W` carries
functions `t_i ∈ Γ(V, W)` such that `k[y_1,…,y_m] → Γ(W, O)`, `y_i ↦ t_i` is surjective, and each
`t_i` is a ratio `P_{j(i)}/P_ℓ` (i.e. `P_{j(i)}|_W = t_i • P_ℓ|_W`), then the chart evaluation
`k[x_0,…,x_N] → Γ(V_ℓ, O)`, `x_j ↦ r_{ℓ,j}` is surjective. -/
theorem projectivizationChartEval_surjective_of_generators {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1))
    {W : V.Opens} (hW : projectivizationChart P ℓ = W) {m : ℕ} (t : Fin m → Γ(V, W))
    (hsurj : Function.Surjective (MvPolynomial.eval₂Hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (W.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
      (fun i => W.topIso.inv.hom (t i))))
    (hcoord : ∀ i, ∃ j, M.res (le_top : W ≤ ⊤) (P j) = t i • M.res (le_top : W ≤ ⊤) (P ℓ)) :
    Function.Surjective (projectivizationChartEval (k := k) P ℓ) :=
  projectivizationChartEvalOver_surjective_of_generators _ P ℓ hW t hsurj hcoord

end
