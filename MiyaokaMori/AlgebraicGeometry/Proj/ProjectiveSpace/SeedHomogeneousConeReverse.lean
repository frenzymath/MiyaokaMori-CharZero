import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedEmbeddingChartOverlap
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeSuccessor
import Mathlib.RingTheory.Localization.Ideal

/-!
# Conditional reverse localization for the homogeneous core

The fraction formulas are keyed by `(k) (N)` and the kernel data by `(emb : X ⟶ ProjectiveSpace N k)`.
The coordinate ratio `X_j / X_i` in chart `i` is `ProjectiveSpaceOverChart.ratioElement (R := k) N j i`
(note the index order); the private value lemma below is about it.

The homogeneous-core construction gives a forward inclusion into every chart
kernel.  The reverse direction needs two separate ingredients: compatibility
of the actual scheme-theoretic kernels on the product overlap, and a
denominator-cleared membership statement for a homogeneous numerator on every
standard chart.  This file records the usable conditional reverse leaf.

It deliberately does not assert chart-kernel equality, saturation, or Proj
recovery.  The overlap theorem is used as an actual hypothesis of the local
restriction result, while the homogeneous numerator condition is the explicit
mathematical obligation still needed for the unconditional reverse theorem.
-/

noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.Proj.SeedHomogeneousConeReverse

universe u


open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ## The concrete homogeneous fraction formula -/

private theorem embeddingChartCoefficientMap_val
    (N : ℕ) (i : Fin (N + 1)) (r : k) :
    (embeddingChartCoefficientMap k N i r).val =
      Localization.mk (MvPolynomial.C r)
        (1 : Submonoid.powers (MvPolynomial.X i)) := by
  rfl

private theorem ratioElement_val
    (N : ℕ) (i j : Fin (N + 1)) :
    (ProjectiveSpaceOverChart.ratioElement (R := k) N j i).val =
      Localization.mk (MvPolynomial.X j)
        (⟨MvPolynomial.X i, 1, by simp⟩ :
          Submonoid.powers (MvPolynomial.X i)) := by
  change Localization.mk (MvPolynomial.X j)
    (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ :
      Submonoid.powers (MvPolynomial.X (R := k) i)) = _
  simp only [pow_one]

private theorem val_embeddingChartLocalizationMap_monomial
    (N : ℕ) (i : Fin (N + 1))
    (m : Fin (N + 1) →₀ ℕ) (r : k) :
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

/-- A homogeneous polynomial is represented by its numerator in the `Away` ring. -/
theorem embeddingChartLocalizationMap_homogeneous
    (N : ℕ) (i : Fin (N + 1))
    {d : ℕ} {p : MvPolynomial (Fin (N + 1)) k} (hp : p.IsHomogeneous d) :
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

variable {k} {X : Scheme.{u}} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)

/-! ## Actual overlap compatibility -/

/--
An element of an actual standard-chart kernel restricts to the actual
scheme-theoretic kernel on the product overlap.  This is the membership form
of `ProjectiveEmbedding.chartKernelAway_restriction`; no polynomial equation
ideal is substituted for the scheme-theoretic kernel.
-/
theorem overlapKernel_mem_of_chartKernel_mem
    (i j : Fin (N + 1)) {z : ProjectiveEmbedding.chartRing k N i}
    (hz : z ∈ ProjectiveEmbedding.chartKernelAway emb i) :
    ProjectiveEmbedding.chartRestrictionAway k N i j z ∈ ProjectiveEmbedding.overlapKernelAway emb i j := by
  rw [← ProjectiveEmbedding.chartKernelAway_restriction emb i j]
  exact Ideal.mem_map_of_mem _ hz

/-! ## Admission-free denominator clearing helper -/

/--
For an actual localization away from `s`, membership of an algebra-map image
of an ideal is exactly membership after multiplying by a power of `s`.  This
is the generic denominator-clearing step used by the conditional reverse inclusion
below; it preserves nilpotents and does not pass to radicals.
-/
theorem algebraMap_mem_map_iff_pow_mul_mem
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : R) [IsLocalization.Away s S] (I : Ideal R) (x : R) :
    algebraMap R S x ∈ I.map (algebraMap R S) ↔
      ∃ n : ℕ, s ^ n * x ∈ I := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers s)]
  constructor
  · rintro ⟨m, hm, hmx⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff m s).mp hm
    exact ⟨n, hmx⟩
  · rintro ⟨n, hn⟩
    exact ⟨s ^ n, (Submonoid.mem_powers_iff _ s).mpr ⟨n, rfl⟩, hn⟩

/-! ## Conditional reverse inclusion contract -/

/--
The conditional reverse localization.  The premise is the
scheme-theoretic compatibility of the two canonical Mathlib `awayMap`s on the
product localization.  It is a local ideal equality, rather than the desired
chart equality or a conclusion-valued witness.  The proof uses
`Away.mk_surjective`, the homogeneous fraction formula above,
`Away.isLocalization_mul`, and `IsLocalization.algebraMap_mem_map_algebraMap_iff`
to clear denominators on each chart before taking the finite common exponent.
-/
theorem embeddingCoreLocalizationEquality_of_overlap
    (hoverlap :
      ∀ i j : Fin (N + 1),
        Ideal.map
            (HomogeneousLocalization.awayMap
              (projectiveGrading k N)
              (MvPolynomial.isHomogeneous_X k j)
              (rfl : MvPolynomial.X i * MvPolynomial.X j =
                MvPolynomial.X i * MvPolynomial.X j))
            (ProjectiveEmbedding.chartKernelAway emb i) =
          Ideal.map
            (HomogeneousLocalization.awayMap
              (projectiveGrading k N)
              (MvPolynomial.isHomogeneous_X k i)
              (mul_comm (MvPolynomial.X i) (MvPolynomial.X j)))
            (ProjectiveEmbedding.chartKernelAway emb j)) :
    embeddingCoreLocalizationEquality emb := by
  unfold embeddingCoreLocalizationEquality
  intro i
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    have hp_raw : p ∈ embeddingRawPolynomialIdeal emb :=
      Ideal.toIdeal_homogeneousCore_le _ _ hp
    rw [embeddingRawPolynomialIdeal, Ideal.mem_iInf] at hp_raw
    simpa [embeddingChartPolynomialKernel] using hp_raw i
  · intro z hz
    obtain ⟨d, p, hp_mem, hpz⟩ :=
      HomogeneousLocalization.Away.mk_surjective
        (projectiveGrading k N) (MvPolynomial.isHomogeneous_X k i) z
    have hp : p.IsHomogeneous d := by simpa using hp_mem
    have hp_map : embeddingChartLocalizationMap k N i p = z := by
      exact (embeddingChartLocalizationMap_homogeneous k N i hp).trans hpz
    have hpK_i : embeddingChartLocalizationMap k N i p ∈ ProjectiveEmbedding.chartKernelAway emb i := by
      simpa [hp_map] using hz
    have hclears : ∀ j : Fin (N + 1),
        ∃ n : ℕ, embeddingChartLocalizationMap k N j
            (p * (MvPolynomial.X i) ^ n) ∈ ProjectiveEmbedding.chartKernelAway emb j := by
      intro j
      have hXiGr : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈
          projectiveGrading k N 1 := by
        simpa using (MvPolynomial.isHomogeneous_X k i)
      have hXjGr : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) k) ∈
          projectiveGrading k N 1 := by
        simpa using (MvPolynomial.isHomogeneous_X k j)
      let uij := HomogeneousLocalization.awayMap
        (projectiveGrading k N)
        hXjGr
        (rfl : MvPolynomial.X i * MvPolynomial.X j =
          MvPolynomial.X i * MvPolynomial.X j)
      let uji := HomogeneousLocalization.awayMap
        (projectiveGrading k N)
        hXiGr
        (mul_comm (MvPolynomial.X i) (MvPolynomial.X j))
      let tji : ProjectiveEmbedding.chartRing k N j :=
        HomogeneousLocalization.Away.mk
          (projectiveGrading k N)
          hXjGr 1 (MvPolynomial.X i) (by
            simpa using (MvPolynomial.isHomogeneous_X k i))
      letI := uji.toAlgebra
      let hloc := HomogeneousLocalization.Away.isLocalization_mul
        (𝒜 := projectiveGrading k N)
        (f := MvPolynomial.X j) (g := MvPolynomial.X i)
        (x := MvPolynomial.X i * MvPolynomial.X j)
        (hf := hXjGr)
        (hg := hXiGr)
        (hx := mul_comm (MvPolynomial.X i) (MvPolynomial.X j))
        (by decide : (1 : ℕ) ≠ 0)
      letI := hloc
      letI : IsLocalization.Away tji
          (HomogeneousLocalization.Away
            (projectiveGrading k N) (MvPolynomial.X i * MvPolynomial.X j)) := by
        simpa [tji, HomogeneousLocalization.Away.isLocalizationElem] using hloc
      have htji : tji = embeddingChartLocalizationMap k N j (MvPolynomial.X i) := by
        simp [tji, embeddingChartLocalizationMap, ProjectiveSpaceOverChart.ratioElement]
      have hmem_i : uij (embeddingChartLocalizationMap k N i p) ∈
          Ideal.map uij (ProjectiveEmbedding.chartKernelAway emb i) :=
        Ideal.mem_map_of_mem _ hpK_i
      have hmem_j : uij (embeddingChartLocalizationMap k N i p) ∈
          Ideal.map uji (ProjectiveEmbedding.chartKernelAway emb j) := by
        change uij (embeddingChartLocalizationMap k N i p) ∈
          Ideal.map uji (ProjectiveEmbedding.chartKernelAway emb j)
        rw [← hoverlap i j]
        exact hmem_i
      have hpGr : p ∈ projectiveGrading k N d := by simpa using hp
      have hmap_j := HomogeneousLocalization.awayMap_mk
        (𝒜 := projectiveGrading k N) (hg := hXiGr)
        (hx := mul_comm (MvPolynomial.X i) (MvPolynomial.X j))
        d hXjGr p (by simpa using hp)
      have hmap_i := HomogeneousLocalization.awayMap_mk
        (𝒜 := projectiveGrading k N) (hg := hXjGr) (hx := rfl)
        d hXiGr p (by simpa using hp)
      have hmap_t := HomogeneousLocalization.awayMap_mk
        (𝒜 := projectiveGrading k N) (hg := hXiGr)
        (hx := mul_comm (MvPolynomial.X i) (MvPolynomial.X j))
        1 hXjGr (MvPolynomial.X i) (by simpa using hXiGr)
      have hfrac : uji (embeddingChartLocalizationMap k N j p) =
          (uji tji) ^ d * uij (embeddingChartLocalizationMap k N i p) := by
        rw [embeddingChartLocalizationMap_homogeneous k N j hp,
          embeddingChartLocalizationMap_homogeneous k N i hp]
        change uji (HomogeneousLocalization.Away.mk
            (projectiveGrading k N) hXjGr d p (by simpa using hp)) =
          (uji tji) ^ d * uij (HomogeneousLocalization.Away.mk
            (projectiveGrading k N) hXiGr d p (by simpa using hp))
        rw [hmap_j, hmap_t, hmap_i]
        apply HomogeneousLocalization.val_injective
        simp only [HomogeneousLocalization.Away.val_mk,
          HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
          Localization.mk_mul, Localization.mk_pow]
        rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        refine ⟨1, ?_⟩
        simp only [map_mul, map_pow, Submonoid.coe_mul, SubmonoidClass.coe_pow,
          Submonoid.coe_one, Subtype.coe_mk, pow_one, mul_pow, one_mul]
        ring
      have hmem_j' : uji (embeddingChartLocalizationMap k N j p) ∈
          Ideal.map uji (ProjectiveEmbedding.chartKernelAway emb j) := by
        rw [hfrac]
        exact Ideal.mul_mem_left (I := Ideal.map uji (ProjectiveEmbedding.chartKernelAway emb j))
          ((uji tji) ^ d) hmem_j
      obtain ⟨n, hn, hnp⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff
          (R := ProjectiveEmbedding.chartRing k N j)
          (S := HomogeneousLocalization.Away
            (projectiveGrading k N) (MvPolynomial.X i * MvPolynomial.X j))
          (Submonoid.powers tji) (ProjectiveEmbedding.chartKernelAway emb j)
          (embeddingChartLocalizationMap k N j p)).mp hmem_j'
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ tji).mp hn
      refine ⟨n, ?_⟩
      have hnp' : (embeddingChartLocalizationMap k N j (MvPolynomial.X i)) ^ n *
          embeddingChartLocalizationMap k N j p ∈ ProjectiveEmbedding.chartKernelAway emb j := by
        simpa [htji] using hnp
      rw [map_mul, map_pow]
      simpa [mul_comm] using hnp'
    -- (`N` is the projective dimension; `Ntot` is the total exponent)
    let Ntot : ℕ := ∑ j : Fin (N + 1), (hclears j).choose
    have hN : p * (MvPolynomial.X i) ^ Ntot ∈ embeddingRawPolynomialIdeal emb := by
      rw [embeddingRawPolynomialIdeal, Ideal.mem_iInf]
      intro j
      change embeddingChartLocalizationMap k N j (p * (MvPolynomial.X i) ^ Ntot) ∈
        ProjectiveEmbedding.chartKernelAway emb j
      let n := (hclears j).choose
      have hn := (hclears j).choose_spec
      have hle : n ≤ Ntot := by
        simpa [n, Ntot] using
          (Finset.single_le_sum
            (fun j _ => Nat.zero_le ((hclears j).choose)) (Finset.mem_univ j))
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
      have hmul := (ProjectiveEmbedding.chartKernelAway emb j).mul_mem_right
        ((embeddingChartLocalizationMap k N j (MvPolynomial.X i)) ^ r) hn
      simpa [n, hr, map_mul, map_pow, mul_assoc, ← pow_add] using hmul
    have hhom : p * (MvPolynomial.X i) ^ Ntot ∈
        projectiveGrading k N (d + Ntot) := by
      have hp' : p ∈ projectiveGrading k N d := by simpa using hp
      have hpow' : (MvPolynomial.X i) ^ Ntot ∈ projectiveGrading k N Ntot := by
        simpa using (MvPolynomial.isHomogeneous_X_pow i Ntot)
      simpa [smul_eq_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (SetLike.mul_mem_graded hp' hpow')
    have hcore : p * (MvPolynomial.X i) ^ Ntot ∈
        (embeddingHomogeneousCore emb).toIdeal :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d + Ntot, hhom⟩ hN
    have hXi : embeddingChartLocalizationMap k N i (MvPolynomial.X i) = 1 := by
      rw [embeddingChartLocalizationMap_X]
      apply HomogeneousLocalization.val_injective
      simpa only [ratioElement_val, HomogeneousLocalization.val_one] using
        (Localization.mk_self_mk
          (M := MvPolynomial (Fin (N + 1)) k)
          (S := Submonoid.powers (MvPolynomial.X i))
          (MvPolynomial.X i)
          ((Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp⟩))
    have hq_map : embeddingChartLocalizationMap k N i
        (p * (MvPolynomial.X i) ^ Ntot) = z := by
      rw [map_mul, map_pow, hXi, one_pow, mul_one]
      exact hp_map
    rw [← hq_map]
    exact Ideal.mem_map_of_mem _ hcore

end AlgebraicGeometry.Proj.SeedHomogeneousConeReverse
