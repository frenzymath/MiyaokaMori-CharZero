import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeSuccessor

/-!
# Homogeneous fractions on the selected embedding charts

Nothing here depends on an embedding: all statements take `(k) (N : ℕ)` explicitly.
The coordinate ratio `X_j / X_i` in chart `i` is `ProjectiveSpaceOverChart.ratioElement (R := k) N j i`
(note the index order); `ratioElement_val` / `ratioElement_self` below are statements about it.

These lemmas calculate the actual dehomogenization map from the selected
embedding's polynomial ring into the degree-zero homogeneous localization.  The
target is the existing `chartRing`; no seed-evaluation kernel or new cone data
is introduced here.
-/

noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.Proj.SeedHomogeneousConeFractions

universe u


open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ## Coordinate, coefficient, and monomial formulas -/

/-- The coefficient embedding has the expected ordinary-localization value. -/
theorem embeddingChartCoefficientMap_val (N : ℕ)
    (i : Fin (N + 1)) (r : k) :
    (embeddingChartCoefficientMap k N i r).val =
      Localization.mk (MvPolynomial.C r)
        (1 : Submonoid.powers (MvPolynomial.X i)) := by
  rfl

/-- The coordinate ratio `X_j / X_i` of chart `i` has the expected ordinary-localization value. -/
theorem ratioElement_val (N : ℕ)
    (i j : Fin (N + 1)) :
    (ProjectiveSpaceOverChart.ratioElement (R := k) N j i).val =
      Localization.mk (MvPolynomial.X j)
        (⟨MvPolynomial.X i, 1, by simp⟩ : Submonoid.powers (MvPolynomial.X i)) := by
  change Localization.mk (MvPolynomial.X j)
    (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ : Submonoid.powers (MvPolynomial.X (R := k) i)) = _
  simp only [pow_one]

/-- The selected coordinate divided by itself is the unit of its chart ring. -/
theorem ratioElement_self (N : ℕ)
    (i : Fin (N + 1)) :
    ProjectiveSpaceOverChart.ratioElement (R := k) N i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one, ratioElement_val]
  exact Localization.mk_self
    (⟨MvPolynomial.X i, 1, by simp⟩ : Submonoid.powers (MvPolynomial.X (R := k) i))

/-- Dehomogenization on a coefficient is the actual chart coefficient map. -/
@[simp]
theorem embeddingChartLocalizationMap_C (N : ℕ)
    (i : Fin (N + 1)) (r : k) :
    embeddingChartLocalizationMap k N i (MvPolynomial.C r) =
      embeddingChartCoefficientMap k N i r := by
  simp [embeddingChartLocalizationMap]

/-- Dehomogenization on a monomial is coefficient times the actual coordinate ratios. -/
@[simp]
theorem embeddingChartLocalizationMap_monomial (N : ℕ)
    (i : Fin (N + 1)) (m : Fin (N + 1) →₀ ℕ) (r : k) :
    embeddingChartLocalizationMap k N i (MvPolynomial.monomial m r) =
      embeddingChartCoefficientMap k N i r *
        m.prod (fun j n ↦ ProjectiveSpaceOverChart.ratioElement (R := k) N j i ^ n) := by
  simp [embeddingChartLocalizationMap]

private theorem val_embeddingChartLocalizationMap_monomial (N : ℕ)
    (i : Fin (N + 1)) (m : Fin (N + 1) →₀ ℕ) (r : k) :
    (embeddingChartLocalizationMap k N i (MvPolynomial.monomial m r)).val =
      Localization.mk (MvPolynomial.monomial m r)
        (⟨MvPolynomial.X i ^ m.degree, m.degree, rfl⟩ :
          Submonoid.powers (MvPolynomial.X (R := k) i)) := by
  change algebraMap (ProjectiveEmbedding.chartRing k N i) (Localization.Away (MvPolynomial.X (R := k) i))
      (embeddingChartLocalizationMap k N i (MvPolynomial.monomial m r)) = _
  rw [embeddingChartLocalizationMap, MvPolynomial.eval₂Hom_monomial]
  rw [MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow,
    HomogeneousLocalization.algebraMap_apply, embeddingChartCoefficientMap_val,
    ratioElement_val, Localization.mk_pow, Localization.mk_prod,
    Localization.mk_mul, one_mul]
  congr 1
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

/-! ## The homogeneous-fraction identity and surjectivity -/

/-- A homogeneous polynomial dehomogenizes to its numerator over `Xᵢ^d`. -/
theorem embeddingChartLocalizationMap_homogeneous (N : ℕ)
    (i : Fin (N + 1)) {d : ℕ} {p : MvPolynomial (Fin (N + 1)) k}
    (hp : p.IsHomogeneous d) :
    embeddingChartLocalizationMap k N i p =
      HomogeneousLocalization.Away.mk (projectiveGrading k N)
        (MvPolynomial.isHomogeneous_X k i) d p (by simpa using hp) := by
  apply HomogeneousLocalization.val_injective
  change (embeddingChartLocalizationMap k N i p).val =
    Localization.mk p
      (⟨MvPolynomial.X i ^ d, d, rfl⟩ :
        Submonoid.powers (MvPolynomial.X (R := k) i))
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      simp [embeddingChartLocalizationMap, Localization.mk_zero]
  | add p q hp hq ihp ihq =>
      rw [map_add, HomogeneousLocalization.val_add, ihp, ihq, Localization.add_mk_self]
  | monomial m r hm =>
      have hdegree : m.degree = d := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hm
      simpa [hdegree] using val_embeddingChartLocalizationMap_monomial k N i m r

/-- The dehomogenization map onto a standard homogeneous-localization chart is surjective. -/
theorem embeddingChartLocalizationMap_surjective (N : ℕ)
    (i : Fin (N + 1)) :
    Function.Surjective (embeddingChartLocalizationMap k N i) := by
  intro z
  obtain ⟨d, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (projectiveGrading k N) (MvPolynomial.isHomogeneous_X k i) z
  exact ⟨p, embeddingChartLocalizationMap_homogeneous k N i (by simpa using hp)⟩

end AlgebraicGeometry.Proj.SeedHomogeneousConeFractions
