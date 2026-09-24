import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProj

/-!
# Coordinate opens cover weighted polynomial Proj

The variables are homogeneous and generate the polynomial algebra over its
actual degree-zero subring. Mathlib's Proj covering theorem therefore gives a
cover by the existing `weightedCoordinateOpen` sets. The pointwise form uses
that same cover and keeps arbitrary coordinate sets and coefficient rings.

Sources: Stacks Project, `algebra.tex`, `definition-proj` and
`lemma-topology-proj`; Section 2 of the paper, the local weighted Proj model
and its coordinate charts in the Veronese polarization argument.
-/

noncomputable section

open AlgebraicGeometry

namespace MiyaokaMori.WeightedJets

universe u v

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (R : Type u) [CommRing R] {ι : Type v} (w : ι → ℕ+)

/-- The actual coordinate opens cover polynomial weighted Proj. -/
theorem weightedCoordinateOpen_iSup :
    ⨆ i, weightedCoordinateOpen R w i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨w i, (MvPolynomial.mem_weightedHomogeneousSubmodule R _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_X R (fun j ↦ (w j : ℕ)) i)⟩
  · apply top_unique
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C r =>
      exact (Algebra.adjoin (weightedPolynomialGrading R w 0)
        (Set.range (MvPolynomial.X : ι → MvPolynomial ι R))).algebraMap_mem
          ⟨MvPolynomial.C r, (MvPolynomial.mem_weightedHomogeneousSubmodule R _ _ _).mpr
            (MvPolynomial.isWeightedHomogeneous_C (fun j ↦ (w j : ℕ)) r)⟩
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- Every point of the same weighted Proj belongs to one of its coordinate opens. -/
theorem exists_mem_weightedCoordinateOpen (x : weightedProj R w) :
    ∃ i, x ∈ weightedCoordinateOpen R w i :=
  TopologicalSpace.Opens.mem_iSup.mp
    ((weightedCoordinateOpen_iSup R w).ge (Set.mem_univ x))

end MiyaokaMori.WeightedJets
