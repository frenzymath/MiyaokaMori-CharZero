import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveSpaceIsIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceDimension
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceGradedRingIsos

/-! # Basic facts about projective space over a field

Basic facts about `P^n_K = Proj K[x_0, …, x_n]`: it is integral, `dim P^n_K = n`, and the homogeneous
coordinates `x_i ∈ Γ(P^n, O(1))` are nonzero sections.

Sources: Hartshorne II.2 (Proj of a domain is integral), Hartshorne I.2.7 / II Ex. 3.20 (`dim P^n = n`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace ProjBundleFiberDegreeOne

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `P^n_K` is integral: `Proj` of the domain `K[x_0, …, x_n]`, which has the nonzero element `x_0`
of degree `1` (`Proj.isIntegral_of_isDomain`). -/
theorem projectiveSpace_isIntegral (K : Type u) [Field K] (n : ℕ) :
    IsIntegral (ProjectiveSpace n K) :=
  Proj.isIntegral_of_isDomain (AlgebraicGeometry.Proj.projectiveGrading K n)
    ⟨1, MvPolynomial.X 0, Nat.one_pos,
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X K 0),
      MvPolynomial.X_ne_zero 0⟩

/-- `topologicalKrullDim P^n_K = n`: transport `weightedProjectiveSpace_one_dimension` (for
`P(1,…,1)` on `ULift (Fin (n+1))`) along the isomorphism `weightedProjectiveSpace_one_iso_projectiveSpace`. -/
theorem projectiveSpace_topologicalKrullDim (K : Type u) [Field K] (n : ℕ) :
    topologicalKrullDim (ProjectiveSpace n K) = ((n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨e, -⟩ := weightedProjectiveSpace_one_iso_projectiveSpace K n
  rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph,
    weightedProjectiveSpace_one_dimension K]
  have hc : Fintype.card (ULift.{u} (Fin (n + 1))) - 1 = n := by simp
  rw [hc]

/-- `dim P^n_K = n`. -/
theorem projectiveSpace_dimension (K : Type u) [Field K] (n : ℕ) :
    (ProjectiveSpace n K).dimension = n := by
  unfold Scheme.dimension
  rw [projectiveSpace_topologicalKrullDim]
  exact ENat.toNat_natCast _

/-- `topologicalKrullDim P^n_K ≠ ⊤`. -/
theorem projectiveSpace_topologicalKrullDim_ne_top (K : Type u) [Field K] (n : ℕ) :
    topologicalKrullDim (ProjectiveSpace n K) ≠ ⊤ := by
  rw [projectiveSpace_topologicalKrullDim]
  intro h
  exact ENat.natCast_ne_top _ (WithBot.coe_injective h)

/-- The homogeneous coordinate `x_i ∈ Γ(P^n, O(1))` is a nonzero section: its value at any point `p`
(there is one, `P^n` being integral) is the fraction `x_i / 1` in the localization of `K[x]` at the
homogeneous prime `p`; if it were `0`, some `s ∉ p` would satisfy `s · x_i = 0`, impossible in a domain. -/
theorem projectiveSpaceCoordinate_ne_zero (K : Type u) [Field K] (n : ℕ) (i : Fin (n + 1)) :
    projectiveSpaceCoordinate K n i ≠ 0 := by
  intro h
  haveI := projectiveSpace_isIntegral K n
  obtain ⟨p⟩ : Nonempty (ProjectiveSpace n K) := inferInstance
  haveI := (p : ProjectiveSpectrum (AlgebraicGeometry.Proj.projectiveGrading K n)).isPrime
  have hv := congrArg (fun s : ((projectiveSpaceTwist K n 1).val.obj (op ⊤) : Type u) =>
    s.1 ⟨p, trivial⟩) h
  have hz : (Localization.mk (MvPolynomial.X i) 1 :
      Localization (p : ProjectiveSpectrum (AlgebraicGeometry.Proj.projectiveGrading K n)).asHomogeneousIdeal.toIdeal.primeCompl) = 0 := hv
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨m, hm⟩ := hz
  rcases mul_eq_zero.mp hm with hm0 | hX
  · exact m.2 (hm0 ▸ Ideal.zero_mem _)
  · exact MvPolynomial.X_ne_zero i hX

end ProjBundleFiberDegreeOne

end
