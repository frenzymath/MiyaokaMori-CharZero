import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveVanishingIdeal
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeFractions
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeOverlapCompatibility
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeReverse

/-! # Localizing the saturated vanishing ideal on the standard charts

Statement: the saturated homogeneous vanishing ideal of a projective embedding, localized on
each standard chart of `Proj`, equals the scheme-theoretic chart kernel of the embedding.

Proof sketch:
1. Using the standard-chart identification of `Proj.awayToSection` with
   `embeddingChartLocalizationMap`, rewrite the chart vanishing condition of every homogeneous
   generator as membership in the chart kernel.
2. The reverse inclusion follows from the denominator-clearing argument of
   `SeedHomogeneousConeReverse.embeddingCoreLocalizationEquality_of_overlap`.
3. The forward inclusion follows from the inclusion of the homogeneous core in every chart
   kernel.

The chart API is keyed by `e.emb : X ⟶ ProjectiveSpace N k` (`chartKernelAway e.emb i`,
`embeddingChartLocalizationMap k N i`, `embeddingHomogeneousCore e.emb`, …).
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveVanishingIdealDeg_iff_chartKernel
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N d : ℕ}
    (e : ProjectiveEmbedding k X N) (F : MvPolynomial (Fin (N + 1)) k) :
    F ∈ projectiveVanishingIdealDeg e.emb.ker d ↔
      F.IsHomogeneous d ∧
        ∀ i : Fin (N + 1),
          AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i F ∈
            AlgebraicGeometry.Proj.ProjectiveEmbedding.chartKernelAway e.emb i := by
  constructor
  · rintro ⟨hF, hsections⟩
    refine ⟨hF, fun i ↦ ?_⟩
    change (AlgebraicGeometry.Proj.ProjectiveEmbedding.chartIso k N i).hom.hom
        (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i F) ∈
      e.emb.ker.ideal (AlgebraicGeometry.Proj.ProjectiveEmbedding.standardAffineOpen k N i)
    rw [AlgebraicGeometry.Proj.SeedHomogeneousConeFractions.embeddingChartLocalizationMap_homogeneous
      k N i hF]
    exact hsections i
  · rintro ⟨hF, hsections⟩
    refine ⟨hF, fun i ↦ ?_⟩
    have hi := hsections i
    change (AlgebraicGeometry.Proj.ProjectiveEmbedding.chartIso k N i).hom.hom
        (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i F) ∈
      e.emb.ker.ideal (AlgebraicGeometry.Proj.ProjectiveEmbedding.standardAffineOpen k N i) at hi
    rw [AlgebraicGeometry.Proj.SeedHomogeneousConeFractions.embeddingChartLocalizationMap_homogeneous
      k N i hF] at hi
    exact hi

theorem embeddingHomogeneousCore_le_projectiveVanishingIdeal
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) :
    (AlgebraicGeometry.Proj.embeddingHomogeneousCore e.emb).toIdeal ≤
      (projectiveVanishingIdeal e.emb.ker).toIdeal := by
  change Ideal.homogeneousCore'
      (AlgebraicGeometry.Proj.projectiveGrading k N)
      (AlgebraicGeometry.Proj.embeddingRawPolynomialIdeal e.emb) ≤ _
  apply Ideal.span_le.mpr
  rintro F ⟨⟨F, hhom⟩, hraw, rfl⟩
  obtain ⟨d, hF⟩ := hhom
  apply Ideal.subset_span
  apply Set.mem_iUnion.mpr
  refine ⟨d, (projectiveVanishingIdealDeg_iff_chartKernel e F).mpr ⟨hF, ?_⟩⟩
  intro i
  change F ∈ ⨅ j, AlgebraicGeometry.Proj.embeddingChartPolynomialKernel e.emb j at hraw
  exact (Ideal.mem_iInf.mp hraw) i

theorem projectiveVanishingIdeal_localizes
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (i : Fin (N + 1)) :
    Ideal.map (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i)
        (projectiveVanishingIdeal e.emb.ker).toIdeal =
      AlgebraicGeometry.Proj.ProjectiveEmbedding.chartKernelAway e.emb i := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    change Ideal.span (⋃ d, projectiveVanishingIdealDeg e.emb.ker d) ≤ _
    apply Ideal.span_le.mpr
    intro F hF
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hF
    exact (projectiveVanishingIdealDeg_iff_chartKernel e F).mp hd |>.2 i
  · have hcore :=
      AlgebraicGeometry.Proj.SeedHomogeneousConeReverse.embeddingCoreLocalizationEquality_of_overlap
        e.emb
        (AlgebraicGeometry.Proj.SeedHomogeneousConeOverlapCompatibility.embeddingChartKernel_canonical_overlap
          e.emb)
    change _ ≤ Ideal.map (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i)
      (projectiveVanishingIdeal e.emb.ker).toIdeal
    rw [← hcore i]
    exact Ideal.map_mono (embeddingHomogeneousCore_le_projectiveVanishingIdeal e)

end
