import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-!
# Irreducibility and dense nonempty opens of the canonical projective line

The zero homogeneous ideal of `k[X₀,X₁]` is prime. It is a point of the
existing projective spectrum because the nonzero positive-degree element
`X₀` belongs to the irrelevant ideal. Its closure contains every homogeneous
prime, so the same canonical `ProjectiveSpace 1 k` is irreducible.

Consequently every actual nonempty open of this projective line is dense.
Both results are ordinary theorems; no global instance or public generic-point
object is added. Reducedness and the nonemptiness of the particular realization
regular locus are separate obligations.

Sources: Theorem 4.2 of the paper (nonconstancy on a general ruling fibre); the
zero homogeneous prime and its specialization order in Mathlib's `ProjectiveSpectrum.Topology`.
-/

noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.Proj.ProjectiveLineIrreducible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The existing projective line over an arbitrary field is an irreducible space. -/
theorem projectiveLine_irreducible : IrreducibleSpace (ProjectiveSpace 1 k) := by
  change IrreducibleSpace (ProjectiveSpectrum (projectiveGrading k 1))
  let η : ProjectiveSpectrum (projectiveGrading k 1) :=
    { asHomogeneousIdeal := ⊥
      isPrime := by
        rw [HomogeneousIdeal.toIdeal_bot]
        infer_instance
      not_irrelevant_le := by
        intro h
        have hX : MvPolynomial.X (0 : Fin 2) ∈
            (⊥ : HomogeneousIdeal (projectiveGrading k 1)) :=
          h (HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading k 1)
            Nat.zero_lt_one (MvPolynomial.isHomogeneous_X k 0))
        change MvPolynomial.X (0 : Fin 2) ∈ (⊥ : Ideal (MvPolynomial (Fin 2) k)) at hX
        exact MvPolynomial.X_ne_zero (0 : Fin 2) (Ideal.mem_bot.mp hX) }
  have hclosure : closure ({η} : Set (ProjectiveSpectrum (projectiveGrading k 1))) =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply (ProjectiveSpectrum.le_iff_mem_closure (projectiveGrading k 1) η x).mp
    change (⊥ : HomogeneousIdeal (projectiveGrading k 1)) ≤ x.asHomogeneousIdeal
    exact bot_le
  apply (irreducibleSpace_def _).mpr
  simpa only [hclosure, Set.top_eq_univ] using
    (isIrreducible_singleton (x := η)).closure

/-- Every actual nonempty open of the same projective line is dense. -/
theorem dense_of_nonempty_open (U : (ProjectiveSpace 1 k).Opens)
    (hU : (U : Set (ProjectiveSpace 1 k)).Nonempty) :
    Dense (U : Set (ProjectiveSpace 1 k)) := by
  have : IrreducibleSpace (ProjectiveSpace 1 k) := projectiveLine_irreducible k
  exact U.isOpen.dense hU

end AlgebraicGeometry.Proj.ProjectiveLineIrreducible
