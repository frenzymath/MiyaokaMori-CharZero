import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjTwisting

/-!
# The standard grading as a weighted grading

The standard grading `projectiveGrading k N` of `k[X_0, …, X_N]` by total degree is the weighted grading
`WeightedJets.weightedPolynomialGrading` with every weight equal to one (`projectiveGrading_eq_weightOne`).
The twist `O(1)` of `P^N_k = Proj (projectiveGrading k N)` and its coordinate sections `Xᵢ / 1` are
`projectiveSpaceTwist k N 1` and `projectiveSpaceCoordinate k N i`; pulling them back along a projective
embedding `e` and then along `f : C → X` gives the sheaf `A = f^* e^* O(1)` and the tuple defining the
twisted cone.

Sources: §2 of the paper (Section 2); Stacks Project, `constructions.tex`, `definition-twist`,
`lemma-proj-sheaves`, `lemma-projective-space`, and the discussion following `definition-projective-space`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Proj
open MiyaokaMori

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The standard grading is exactly the existing positive-weight grading with every weight one. -/
theorem projectiveGrading_eq_weightOne (N : ℕ) :
    projectiveGrading k N =
      WeightedJets.weightedPolynomialGrading k (fun _ : Fin (N + 1) ↦ (1 : ℕ+)) := rfl

end AlgebraicGeometry.Proj
