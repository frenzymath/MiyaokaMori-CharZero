import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedEmbeddingChartOverlap
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeSuccessor

/-!
# Canonical homogeneous-localization overlap compatibility

The chart data are keyed by `(k) (N)` and the kernel data by `(emb : X ⟶ ProjectiveSpace N k)`.

The two standard chart kernel ideals are restricted to one product open
`D₊(Xᵢ * Xⱼ)`.  This file compares both restriction maps with Mathlib's
canonical `HomogeneousLocalization.awayMap` whose target is that same product
localization.  The comparison is scheme-theoretic: the ideals are transported
from the kernel ideal sheaf, so nilpotents are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj.SeedHomogeneousConeOverlapCompatibility

universe u



attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

private lemma overlap_le_standard_right (N : ℕ)
    (i j : Fin (N + 1)) :
    ProjectiveEmbedding.overlapOpen k N i j ≤ ProjectiveSpaceOver.chart N k j := by
  exact Proj.basicOpen_mono (projectiveGrading k N)
    (MvPolynomial.X j) (MvPolynomial.X i * MvPolynomial.X j)
    ⟨MvPolynomial.X i, by simp [mul_comm]⟩

private lemma overlapAffineOpen_le_standardAffineOpen_right
    (N : ℕ) (i j : Fin (N + 1)) :
    ProjectiveEmbedding.overlapAffineOpen k N i j ≤ ProjectiveEmbedding.standardAffineOpen k N j := by
  exact overlap_le_standard_right k N i j

private def chartRestrictionGammaRight (N : ℕ)
    (i j : Fin (N + 1)) :
    Γ(ProjectiveSpace N k, ProjectiveEmbedding.standardAffineOpen k N j) →+*
      Γ(ProjectiveSpace N k, ProjectiveEmbedding.overlapAffineOpen k N i j) :=
  ((ProjectiveSpace N k).presheaf.map
    (homOfLE (overlapAffineOpen_le_standardAffineOpen_right k N i j)).op).hom

private def chartRestrictionAwayRight (N : ℕ)
    (i j : Fin (N + 1)) : ProjectiveEmbedding.chartRing k N j →+*
      HomogeneousLocalization.Away (projectiveGrading k N)
        (MvPolynomial.X i * MvPolynomial.X j) :=
  (ProjectiveEmbedding.overlapIso k N i j).inv.hom.comp
    ((chartRestrictionGammaRight k N i j).comp (ProjectiveEmbedding.chartIso k N j).hom.hom)

private theorem chartRestrictionAway_left_eq_awayMap
    (N : ℕ) (i j : Fin (N + 1)) :
    ProjectiveEmbedding.chartRestrictionAway k N i j =
      HomogeneousLocalization.awayMap
        (projectiveGrading k N)
        (f := MvPolynomial.X i) (g := MvPolynomial.X j)
        (hg := MvPolynomial.isHomogeneous_X k j)
        (hx := (rfl : MvPolynomial.X i * MvPolynomial.X j =
          MvPolynomial.X i * MvPolynomial.X j)) := by
  apply RingHom.ext
  intro z
  apply (ProjectiveEmbedding.overlapIso k N i j).commRingCatIsoToRingEquiv.injective
  change ((ProjectiveEmbedding.overlapIso k N i j).hom.hom.comp (ProjectiveEmbedding.chartRestrictionAway k N i j)) z = _
  unfold ProjectiveEmbedding.chartRestrictionAway
  rw [← RingHom.comp_assoc]
  have hcancel :
      (ProjectiveEmbedding.overlapIso k N i j).hom.hom.comp (ProjectiveEmbedding.overlapIso k N i j).inv.hom =
        RingHom.id _ := by
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using
      congrArg (fun q => q.hom) (ProjectiveEmbedding.overlapIso k N i j).inv_hom_id
  rw [hcancel]
  change (ProjectiveEmbedding.chartRestrictionGamma k N i j) ((ProjectiveEmbedding.chartIso k N i).hom.hom z) = _
  have haway :=
    Proj.awayMap_awayToSection
      (𝒜 := projectiveGrading k N)
      (f := MvPolynomial.X i) (g := MvPolynomial.X j)
      (g_deg := by
        simpa [projectiveGrading] using MvPolynomial.isHomogeneous_X k j)
      (x := MvPolynomial.X i * MvPolynomial.X j) (hx := rfl)
  have haway' := congrArg CommRingCat.Hom.hom haway
  exact (congrArg (fun f ↦ f z) haway').symm

private theorem chartRestrictionAway_right_eq_awayMap
    (N : ℕ) (i j : Fin (N + 1)) :
    chartRestrictionAwayRight k N i j =
      HomogeneousLocalization.awayMap
        (projectiveGrading k N)
        (f := MvPolynomial.X j) (g := MvPolynomial.X i)
        (hg := MvPolynomial.isHomogeneous_X k i)
        (hx := (mul_comm (MvPolynomial.X i) (MvPolynomial.X j))) := by
  apply RingHom.ext
  intro z
  apply (ProjectiveEmbedding.overlapIso k N i j).commRingCatIsoToRingEquiv.injective
  change ((ProjectiveEmbedding.overlapIso k N i j).hom.hom.comp (chartRestrictionAwayRight k N i j)) z = _
  unfold chartRestrictionAwayRight
  rw [← RingHom.comp_assoc]
  have hcancel :
      (ProjectiveEmbedding.overlapIso k N i j).hom.hom.comp (ProjectiveEmbedding.overlapIso k N i j).inv.hom =
        RingHom.id _ := by
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using
      congrArg (fun q => q.hom) (ProjectiveEmbedding.overlapIso k N i j).inv_hom_id
  rw [hcancel]
  change (chartRestrictionGammaRight k N i j) ((ProjectiveEmbedding.chartIso k N j).hom.hom z) = _
  have haway :=
    Proj.awayMap_awayToSection
      (𝒜 := projectiveGrading k N)
      (f := MvPolynomial.X j) (g := MvPolynomial.X i)
      (g_deg := by
        simpa [projectiveGrading] using MvPolynomial.isHomogeneous_X k i)
      (x := MvPolynomial.X i * MvPolynomial.X j)
      (hx := mul_comm (MvPolynomial.X i) (MvPolynomial.X j))
  have haway' := congrArg CommRingCat.Hom.hom haway
  exact (congrArg (fun f ↦ f z) haway').symm

variable {k} {X : Scheme.{u}} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)

private theorem chartKernelGamma_restriction_right
    (i j : Fin (N + 1)) :
    Ideal.map (chartRestrictionGammaRight k N i j) (ProjectiveEmbedding.chartKernelGamma emb j) =
      ProjectiveEmbedding.overlapKernelGamma emb i j := by
  change Ideal.map
      ((ProjectiveSpace N k).presheaf.map
        (homOfLE (overlapAffineOpen_le_standardAffineOpen_right k N i j)).op).hom
      (emb.ker.ideal (ProjectiveEmbedding.standardAffineOpen k N j)) =
    emb.ker.ideal (ProjectiveEmbedding.overlapAffineOpen k N i j)
  exact emb.ker.map_ideal
    (overlapAffineOpen_le_standardAffineOpen_right k N i j)

private theorem chartKernelAway_left_map
    (i j : Fin (N + 1)) :
    Ideal.map
        (HomogeneousLocalization.awayMap
          (projectiveGrading k N)
          (f := MvPolynomial.X i) (g := MvPolynomial.X j)
          (hg := MvPolynomial.isHomogeneous_X k j)
          (hx := (rfl : MvPolynomial.X i * MvPolynomial.X j =
            MvPolynomial.X i * MvPolynomial.X j)))
        (ProjectiveEmbedding.chartKernelAway emb i) = ProjectiveEmbedding.overlapKernelAway emb i j := by
  rw [← chartRestrictionAway_left_eq_awayMap k N i j]
  exact ProjectiveEmbedding.chartKernelAway_restriction emb i j

private theorem chartKernelAway_right_map
    (i j : Fin (N + 1)) :
    Ideal.map
        (HomogeneousLocalization.awayMap
          (projectiveGrading k N)
          (f := MvPolynomial.X j) (g := MvPolynomial.X i)
          (hg := MvPolynomial.isHomogeneous_X k i)
          (hx := (mul_comm (MvPolynomial.X i) (MvPolynomial.X j))))
        (ProjectiveEmbedding.chartKernelAway emb j) = ProjectiveEmbedding.overlapKernelAway emb i j := by
  rw [← chartRestrictionAway_right_eq_awayMap k N i j]
  unfold chartRestrictionAwayRight ProjectiveEmbedding.chartKernelAway
    ProjectiveEmbedding.overlapKernelAway
  rw [← chartKernelGamma_restriction_right emb i j]
  exact AlgebraicGeometry.Proj.ProjectiveEmbedding.map_comp_ringEquiv_restriction
    (ProjectiveEmbedding.chartIso k N j).commRingCatIsoToRingEquiv
    (chartRestrictionGammaRight k N i j)
    (ProjectiveEmbedding.overlapIso k N i j).symm.commRingCatIsoToRingEquiv
    (ProjectiveEmbedding.chartKernelGamma emb j)

/-- The two canonical chart-kernel images agree in the same product Away ring. -/
theorem embeddingChartKernel_canonical_overlap (i j : Fin (N + 1)) :
    Ideal.map
        (HomogeneousLocalization.awayMap
          (projectiveGrading k N)
          (f := MvPolynomial.X i) (g := MvPolynomial.X j)
          (hg := MvPolynomial.isHomogeneous_X k j)
          (hx := (rfl : MvPolynomial.X i * MvPolynomial.X j =
            MvPolynomial.X i * MvPolynomial.X j)))
        (ProjectiveEmbedding.chartKernelAway emb i) =
      Ideal.map
        (HomogeneousLocalization.awayMap
          (projectiveGrading k N)
          (f := MvPolynomial.X j) (g := MvPolynomial.X i)
          (hg := MvPolynomial.isHomogeneous_X k i)
          (hx := (mul_comm (MvPolynomial.X i) (MvPolynomial.X j))))
        (ProjectiveEmbedding.chartKernelAway emb j) := by
  exact (chartKernelAway_left_map emb i j).trans
    (chartKernelAway_right_map emb i j).symm

end AlgebraicGeometry.Proj.SeedHomogeneousConeOverlapCompatibility
