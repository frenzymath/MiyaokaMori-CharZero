import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The grading on the Rees algebra

The degree `n` submodule of Mathlib's actual `reesAlgebra I` consists of its polynomials
supported in degree `n`. Coefficient uniqueness makes these submodules independent, and
the finite monomial expansion spans the whole Rees algebra. Their multiplication is the
usual multiplication of monomials. The resulting graded projection is the actual degree
`n` monomial of the original polynomial.

This is an algebraic foundation for the point blowups used in the ruled-surface realization and the
prescribed-point specialization of the paper. It does not construct a blowup or identify its
exceptional fiber.
-/

open scoped BigOperators

namespace MiyaokaMori.RingTheory.ReesAlgebra

universe u

variable {R : Type u} [CommRing R]

/-- The degree `n` monomials inside the same Rees subalgebra of `R[X]`. -/
noncomputable def grading (I : Ideal R) (n : ℕ) : Submodule R (reesAlgebra I) :=
  (LinearMap.range (Polynomial.monomial n : R →ₗ[R] Polynomial R)).comap
    (reesAlgebra I).val.toLinearMap

/-- Membership in a homogeneous part is actual equality with a monomial. -/
theorem mem_grading_iff (I : Ideal R) (n : ℕ) (f : reesAlgebra I) :
    f ∈ grading I n ↔ ∃ r : R, Polynomial.monomial n r = (f : Polynomial R) :=
  Iff.rfl

/-- A homogeneous Rees element is recovered from its coefficient in its degree. -/
theorem eq_monomial_of_mem (I : Ideal R) {n : ℕ} {f : reesAlgebra I}
    (hf : f ∈ grading I n) :
    (f : Polynomial R) = Polynomial.monomial n ((f : Polynomial R).coeff n) := by
  obtain ⟨r, hr⟩ := (mem_grading_iff I n f).mp hf
  rw [← hr, Polynomial.coeff_monomial_same]

/-- A homogeneous Rees element has zero coefficient in any other degree. -/
theorem coeff_eq_zero_of_mem (I : Ideal R) {n m : ℕ} {f : reesAlgebra I}
    (hf : f ∈ grading I n) (hnm : n ≠ m) : (f : Polynomial R).coeff m = 0 := by
  rw [eq_monomial_of_mem I hf, Polynomial.coeff_monomial, if_neg hnm]

/-- Constants and products have the expected degrees in the actual Rees algebra. -/
instance gradedMonoid (I : Ideal R) : SetLike.GradedMonoid (grading I) where
  one_mem := (mem_grading_iff I 0 1).mpr ⟨1, by simp⟩
  mul_mem := by
    intro i j f g hf hg
    obtain ⟨a, ha⟩ := (mem_grading_iff I i f).mp hf
    obtain ⟨b, hb⟩ := (mem_grading_iff I j g).mp hg
    apply (mem_grading_iff I (i + j) (f * g)).mpr
    refine ⟨a * b, ?_⟩
    change Polynomial.monomial (i + j) (a * b) = (f : Polynomial R) * (g : Polynomial R)
    rw [← ha, ← hb, Polynomial.monomial_mul_monomial]

/-- The degree `n` monomial of a Rees element remains in the same Rees algebra. -/
noncomputable def component (I : Ideal R) (n : ℕ) (f : reesAlgebra I) : reesAlgebra I :=
  ⟨Polynomial.monomial n ((f : Polynomial R).coeff n),
    reesAlgebra.monomial_mem.mpr (f.property n)⟩

/-- The actual coefficient monomial belongs to the corresponding homogeneous part. -/
theorem component_mem (I : Ideal R) (n : ℕ) (f : reesAlgebra I) :
    component I n f ∈ grading I n :=
  (mem_grading_iff I n _).mpr ⟨(f : Polynomial R).coeff n, rfl⟩

/-- The finite monomial expansion holds inside the Rees algebra itself. -/
theorem sum_components (I : Ideal R) (f : reesAlgebra I) :
    ∑ n ∈ (f : Polynomial R).support, component I n f = f := by
  apply Subtype.ext
  change (reesAlgebra I).val (∑ n ∈ (f : Polynomial R).support, component I n f) = _
  rw [map_sum]
  exact (f : Polynomial R).as_sum_support.symm

/-- Different homogeneous parts are independent, detected by polynomial coefficients. -/
theorem grading_iSupIndep (I : Ideal R) : iSupIndep (grading I) := by
  rw [iSupIndep_def]
  intro n
  apply Submodule.disjoint_def.mpr
  intro f hf hother
  let c : reesAlgebra I →ₗ[R] R :=
    (Polynomial.lcoeff R n).comp (reesAlgebra I).val.toLinearMap
  have hle : (⨆ (m : ℕ) (_ : m ≠ n), grading I m) ≤ LinearMap.ker c := by
    refine iSup_le fun m ↦ iSup_le fun hmn ↦ ?_
    intro g hg
    exact coeff_eq_zero_of_mem I hg hmn
  have hzero : (f : Polynomial R).coeff n = 0 := hle hother
  apply Subtype.ext
  rw [eq_monomial_of_mem I hf, hzero, map_zero]
  rfl

/-- The homogeneous parts span every element of the actual Rees algebra. -/
theorem grading_iSup_eq_top (I : Ideal R) : (⨆ n, grading I n) = ⊤ := by
  apply top_unique
  intro f _
  rw [← sum_components I f]
  exact Submodule.sum_mem _ fun n _ ↦ Submodule.mem_iSup_of_mem n (component_mem I n f)

/-- The canonical sum of homogeneous Rees elements is bijective. -/
theorem isInternal (I : Ideal R) : DirectSum.IsInternal (grading I) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (grading_iSupIndep I) (grading_iSup_eq_top I)

/-- The natural-number grading on the same Mathlib Rees algebra. -/
noncomputable instance gradedAlgebra (I : Ideal R) : GradedAlgebra (grading I) :=
  (isInternal I).gradedAlgebra

/-- A graded projection is exactly the original polynomial's coefficient monomial. -/
theorem coe_graded_proj (I : Ideal R) (n : ℕ) (f : reesAlgebra I) :
    ((GradedRing.proj (grading I) n f : reesAlgebra I) : Polynomial R) =
      Polynomial.monomial n ((f : Polynomial R).coeff n) := by
  classical
  have hproj : ∀ m, GradedRing.proj (grading I) n (component I m f) =
      if m = n then component I n f else 0 := by
    intro m
    by_cases hmn : m = n
    · subst m
      rw [if_pos rfl, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_same (grading I) (component_mem I n f)
    · rw [if_neg hmn, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (grading I) (component_mem I m f) hmn
  have hsum : GradedRing.proj (grading I) n f = component I n f := by
    conv_lhs => rw [← sum_components I f]
    rw [map_sum]
    simp only [hproj]
    by_cases hn : n ∈ (f : Polynomial R).support
    · simp [hn]
    · have hcoeff : (f : Polynomial R).coeff n = 0 :=
        Polynomial.notMem_support_iff.mp hn
      have hc : component I n f = 0 := by
        apply Subtype.ext
        simp [component, hcoeff]
      simp [hc]
  exact congrArg (fun g : reesAlgebra I ↦ (g : Polynomial R)) hsum

end MiyaokaMori.RingTheory.ReesAlgebra
