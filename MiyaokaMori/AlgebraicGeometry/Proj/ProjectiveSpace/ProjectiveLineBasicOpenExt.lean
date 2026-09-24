import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-!
# Identifying projective-line points by homogeneous basic opens

Two actual points of the canonical projective line over a field are equal if they belong to
the same basic opens for every positive-degree homogeneous polynomial. Mathlib already supplies
`HomogeneousIdeal.ext'` for all homogeneous degrees; the degree-zero case here follows because
degree-zero polynomials are constants and a proper prime ideal contains no nonzero constant.

This supplies the underlying-point comparison for the prescribed-point reparametrization
(Lemma 5.1 of the paper). The source for homogeneous basic opens and their
point-separating role is Stacks Tag 00JP. No coordinate classification or automorphism is assumed.
-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj

universe u

namespace AlgebraicGeometry.Proj.ProjectiveLineBasicOpenExt

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- Actual points of the canonical projective line are equal if every positive-degree
homogeneous polynomial has the same basic-open membership at both points. -/
theorem point_eq_of_pos_homogeneous_basicOpen (x y : ProjectiveSpace 1 k)
    (h : ∀ (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin 2) k), f.IsHomogeneous n →
      (x ∈ Proj.basicOpen (projectiveGrading k 1) f ↔
        y ∈ Proj.basicOpen (projectiveGrading k 1) f)) : x = y := by
  dsimp only [ProjectiveSpace, ProjectiveSpaceOver] at x y h ⊢
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n f hf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hdeg : f.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr hf
    have hfC : f = MvPolynomial.C (f.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
    by_cases hr : f.coeff 0 = 0
    · rw [hfC, hr, map_zero]
      exact iff_of_true (zero_mem _) (zero_mem _)
    · have hu : IsUnit f := by
        rw [hfC]
        exact (isUnit_iff_ne_zero.mpr hr).map MvPolynomial.C
      have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
      have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
      exact iff_of_false
        (Ideal.notMem_of_isUnit x.asHomogeneousIdeal.toIdeal hu)
        (Ideal.notMem_of_isUnit y.asHomogeneousIdeal.toIdeal hu)
  · have hnot := h n hn f hf
    change (f ∉ x.asHomogeneousIdeal ↔ f ∉ y.asHomogeneousIdeal) at hnot
    exact not_iff_not.mp hnot

end AlgebraicGeometry.Proj.ProjectiveLineBasicOpenExt
