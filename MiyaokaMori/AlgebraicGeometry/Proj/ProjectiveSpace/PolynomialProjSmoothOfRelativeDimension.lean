import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.PolynomialProjChartRingEquiv

/-! # Smoothness of the polynomial Proj of the expected relative dimension

**Statement.** Let `R` be a commutative ring and `σ` a finite type with `|σ| = n + 1`. The structure
morphism `Proj R[x_σ] → Spec R` of projective `n`-space over `R` (Mathlib's `Proj` of the standard-graded
polynomial ring, followed by `Spec` of `R → R[x_σ]_0`) is smooth of relative dimension `n`
(`SmoothOfRelativeDimension n`).

**Source.** Hartshorne II.2.5 and Exercise II.2.14 (the standard affine cover `D_+(x_j) ≅ A^n_R` of `P^n_R`);
Stacks 01NE; Stacks 01V5/01V7 (smoothness is local on the source; `A^n_R → Spec R` is smooth of relative
dimension `n`). Paper: Lemma 2.3 (`Y_k^{GG}` is locally `U × P(w)`).

**Proof.**
1. `SmoothOfRelativeDimension n` is Zariski-local on the source (it is a `HasRingHomProperty`, Mathlib
   `Morphisms/Smooth.lean`; `HasRingHomProperty.instIsZariskiLocalAtSource`), so by
   `IsZariskiLocalAtSource.iff_of_iSup_eq_top` it suffices to check it on the cover of `Proj R[x_σ]` by the
   standard opens `D_+(x_j)`, `j : σ`. They cover because the `x_j` generate `R[x_σ]` over
   `R[x_σ]_0 ⊇ R` (`MvPolynomial.adjoin_range_X`, `Proj.iSup_basicOpen_eq_top'`).
2. `D_+(x_j) ≅ Spec (R[x_σ]_{x_j})_0` (`Proj.basicOpenIsoSpec`, `x_j` homogeneous of degree `1 > 0`), and
   the composite `Spec (R[x_σ]_{x_j})_0 → Proj R[x_σ] → Spec R[x_σ]_0 → Spec R` is `Spec` of the ring map
   `R → R[x_σ]_0 → (R[x_σ]_{x_j})_0` (`Proj.awayι_toSpecZero`, `Spec.map_comp`); by
   `HasRingHomProperty.Spec_iff` we must show this ring map is locally standard smooth of relative
   dimension `n`, and by `RingHom.locally_of` it suffices that it is standard smooth of relative dimension
   `n` (the property respects isomorphisms, `RingHom.isStandardSmoothOfRelativeDimension_respectsIso`).
3. Dehomogenisation identifies `(R[x_σ]_{x_j})_0 ≅ R[y_k : k ≠ j]` over `R`
   (`MvPolynomial.StandardProjChart.chartRingEquiv`), so it
   suffices that `R → R[y_τ]` is standard smooth of relative dimension `|τ| = n`.
4. The polynomial algebra `R[y_τ]` has the submersive presentation with generators `τ` and no relations
   (`Algebra.Generators.mvPolynomial`, kernel `⊥`, empty Jacobian of determinant `1`), of dimension
   `|τ| - 0 = n` (`SubmersivePresentation.isStandardSmoothOfRelativeDimension`), and
   `|{k // k ≠ j}| = |σ| - 1 = n` (`Fintype.card_subtype_compl`).

Edge cases: `R = 0`: `Proj` is empty and every property holds vacuously (the proof does not divide by
anything). `n = 0` (`σ` a singleton): `Proj R[x] = Spec R` and the statement says `Spec R → Spec R` is
smooth of relative dimension `0`, which is what the presentation with no generators gives.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace MvPolynomial.StandardProjChart

section Polynomial

variable (R : Type u) [CommRing R] (τ : Type u)

/-- The submersive presentation of `R[y_τ]` with generators `τ` and no relations. -/
def polynomialPresentation : Algebra.SubmersivePresentation R (MvPolynomial τ R) τ (Fin 0) where
  toGenerators := Algebra.Generators.mvPolynomial R τ
  relation := Fin.elim0
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty, Algebra.Generators.ker_mvPolynomial]
  map := Fin.elim0
  map_inj := fun a b _ => Fin.elim0 a
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

/-- `R[y_τ]` is standard smooth of relative dimension `|τ|` over `R`. -/
theorem mvPolynomial_isStandardSmoothOfRelativeDimension [Fintype τ] (n : ℕ)
    (hτ : Fintype.card τ = n) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial τ R) :=
  (polynomialPresentation R τ).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension, Nat.card_eq_fintype_card, hτ])

/-- `C : R → R[y_τ]` is standard smooth of relative dimension `|τ|`. -/
theorem C_isStandardSmoothOfRelativeDimension [Fintype τ] (n : ℕ) (hτ : Fintype.card τ = n) :
    RingHom.IsStandardSmoothOfRelativeDimension n (MvPolynomial.C : R →+* MvPolynomial τ R) := by
  rw [← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact mvPolynomial_isStandardSmoothOfRelativeDimension R τ n hτ

end Polynomial

section Chart

variable (R : Type u) [CommRing R] {σ : Type u} [DecidableEq σ] (j : σ)

/-- The structure map `R → (R[x_σ]_{x_j})_0` (through the degree-zero part). -/
def chartStructureHom :
    R →+* HomogeneousLocalization.Away (grading R (σ := σ)) (MvPolynomial.X j) :=
  (HomogeneousLocalization.fromZeroRingHom (grading R (σ := σ))
    (Submonoid.powers (MvPolynomial.X j : MvPolynomial σ R))).comp (algebraMap R (grading R (σ := σ) 0))

/-- The inverse dehomogenisation carries `C` to the structure map of the chart. -/
theorem chartRingEquiv_symm_comp_C :
    (chartRingEquiv R j).symm.toRingHom.comp (MvPolynomial.C : R →+* MvPolynomial {k : σ // k ≠ j} R) =
      chartStructureHom R j := by
  refine RingHom.ext fun c => ?_
  have h := RingHom.congr_fun (chartRingEquiv_comp_fromZeroRingHom_comp_algebraMap R j) c
  change (chartRingEquiv R j).symm (MvPolynomial.C c) = chartStructureHom R j c
  rw [← h]
  exact (chartRingEquiv R j).symm_apply_apply _

/-- The coordinate ring of the standard chart `D_+(x_j)` is standard smooth of relative dimension
`|σ| - 1` over `R`. -/
theorem chartStructureHom_isStandardSmoothOfRelativeDimension [Fintype σ] (n : ℕ)
    (hσ : Fintype.card σ = n + 1) :
    RingHom.IsStandardSmoothOfRelativeDimension n (chartStructureHom R j) := by
  have hcard : Fintype.card {k : σ // k ≠ j} = n := by
    have := Fintype.card_subtype_compl (fun k : σ => k = j)
    rw [Fintype.card_subtype_eq, hσ] at this
    simpa using this
  rw [← chartRingEquiv_symm_comp_C]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ (chartRingEquiv R j).symm
    (C_isStandardSmoothOfRelativeDimension R _ n hcard)

end Chart

section Proj

variable (R : Type u) [CommRing R] (σ : Type u) [Fintype σ] [DecidableEq σ]

/-- The structure morphism `Proj R[x_σ] → Spec R` of projective space over `R`. -/
def projToSpecBase : Proj (grading R (σ := σ)) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (grading R (σ := σ) 0)))

/-- The variables generate `R[x_σ]` over the degree-zero part. -/
theorem adjoin_range_X_eq_top :
    Algebra.adjoin (grading R (σ := σ) 0) (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  have hp : p ∈ Algebra.adjoin R (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
    rw [MvPolynomial.adjoin_range_X]; trivial
  induction hp using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    have : algebraMap R (MvPolynomial σ R) r =
        algebraMap (grading R (σ := σ) 0) (MvPolynomial σ R) (algebraMap R (grading R (σ := σ) 0) r) :=
      rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- `D_+(x_j)`, `j : σ`, cover `Proj R[x_σ]`. -/
theorem iSup_basicOpen_X_eq_top :
    ⨆ j : σ, Proj.basicOpen (grading R (σ := σ)) (MvPolynomial.X j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _ (fun j => ⟨1, X_mem R j⟩) (adjoin_range_X_eq_top R σ)

/-- **Projective space is smooth**: `Proj R[x_σ] → Spec R` is smooth of relative dimension `|σ| - 1`. -/
theorem projToSpecBase_smoothOfRelativeDimension (n : ℕ) (hσ : Fintype.card σ = n + 1) :
    SmoothOfRelativeDimension n (projToSpecBase R σ) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} n)
  have hiso : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} n) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @SmoothOfRelativeDimension.{u} n)]
    exact AlgebraicGeometry.affineLocally_respectsIso
      (P := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
      (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} n) _
    (iSup_basicOpen_X_eq_top R σ)]
  intro j
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension.{u} n)
    (Proj.basicOpenIsoSpec (grading R (σ := σ)) (MvPolynomial.X j) (X_mem R j) Nat.one_pos).inv,
    ← Category.assoc, ← Proj.awayι, projToSpecBase, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} n)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact chartStructureHom_isStandardSmoothOfRelativeDimension R j n hσ

end Proj

end MvPolynomial.StandardProjChart

end
