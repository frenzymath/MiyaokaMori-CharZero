import MiyaokaMori.RingTheory.PolynomialTupleHomogenization
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Removing the common factor of a polynomial coordinate tuple

For the same nonzero finite tuple `P`, the common factor is its normalized finite gcd and the
reduced coordinates are the actual Euclidean quotients. Their maximum degree drops by exactly
the degree of that gcd. Homogenization uses `[1 : t]`, preserving the project's zero `[1 : 0]`.
The reduced homogeneous coordinates have no common zero over any field extension, including
at `[0 : 1]`, and the original homogeneous tuple has the stated common homogeneous factor.

These are algebraic statements. The maximum polynomial degree is not defined to be the degree
of a pulled-back line module. The actual projective morphism, its pullback of the existing
`O(1)`, and the Cartier/zero-cycle degree comparison remain separate geometric obligations.

Sources: the proof of Theorem 4.2 of the paper; Stacks Project, `algebra.tex`,
`lemma-polynomial-domain-normal` and `lemma-homogenize`; `constructions.tex`,
`lemma-projective-space`. No projective-space or twisting-sheaf definition is introduced here.
-/

noncomputable section

open Polynomial

-- `NormalizedGCDMonoid k[X]` goes through
-- `CommGroupWithZero.instStrongNormalizedGCDMonoid`, which needs `[DecidableEq k]`;
-- for a bare `[Field k]` it is only available classically.
open scoped Classical

namespace MiyaokaMori.RingTheory.PrimitivePolynomialTuple

open PolynomialTupleHomogenization

universe u v

variable {k : Type u} [Field k] {N : ℕ}

/-- The normalized finite gcd of the actual coordinate polynomials. -/
def commonFactor (P : Fin (N + 1) → k[X]) : k[X] := Finset.univ.gcd P

/-- The reduced coordinates are the actual Euclidean quotients by the finite gcd. -/
def reduced (P : Fin (N + 1) → k[X]) (i : Fin (N + 1)) : k[X] :=
  P i / commonFactor P

/-- The maximum of the natural degrees, allowing zero coordinate polynomials. -/
def maxDegree (P : Fin (N + 1) → k[X]) : ℕ :=
  Finset.univ.sup fun i ↦ (P i).natDegree

/-- Each coordinate has degree at most the tuple's actual maximum. -/
theorem natDegree_le_maxDegree (P : Fin (N + 1) → k[X]) (i : Fin (N + 1)) :
    (P i).natDegree ≤ maxDegree P :=
  Finset.le_sup (f := fun j ↦ (P j).natDegree) (Finset.mem_univ i)

/-- A degree bound on every coordinate bounds the same finite maximum. -/
theorem maxDegree_le (P : Fin (N + 1) → k[X]) {r : ℕ}
    (h : ∀ i, (P i).natDegree ≤ r) : maxDegree P ≤ r :=
  Finset.sup_le fun i _ ↦ h i

/-- A nonzero tuple has a nonzero coordinate attaining its maximum, even in degree zero. -/
theorem exists_nonzero_at_maxDegree (P : Fin (N + 1) → k[X])
    (hP : ∃ i, P i ≠ 0) : ∃ i, P i ≠ 0 ∧ (P i).natDegree = maxDegree P := by
  by_cases hd : maxDegree P = 0
  · obtain ⟨i, hi⟩ := hP
    refine ⟨i, hi, le_antisymm (natDegree_le_maxDegree P i) ?_⟩
    simp [hd]
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i ↦ (P i).natDegree)
    change maxDegree P = (P i).natDegree at hi
    refine ⟨i, ?_, hi.symm⟩
    intro hzero
    apply hd
    simpa only [hzero, Polynomial.natDegree_zero] using hi

/-- Some coefficient in the maximum degree is nonzero; zero components cause no exception. -/
theorem exists_topCoefficient_ne_zero (P : Fin (N + 1) → k[X])
    (hP : ∃ i, P i ≠ 0) : ∃ i, (P i).coeff (maxDegree P) ≠ 0 := by
  obtain ⟨i, hi, hdegree⟩ := exists_nonzero_at_maxDegree P hP
  refine ⟨i, ?_⟩
  rw [← hdegree, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hi

/-- A genuinely nonzero tuple has a nonzero common factor. -/
theorem commonFactor_ne_zero (P : Fin (N + 1) → k[X]) (hP : ∃ i, P i ≠ 0) :
    commonFactor P ≠ 0 := by
  obtain ⟨i, hi⟩ := hP
  exact Finset.gcd_ne_zero_iff.mpr ⟨i, Finset.mem_univ i, hi⟩

/-- The common factor divides each of the original coordinates. -/
theorem commonFactor_dvd (P : Fin (N + 1) → k[X]) (i : Fin (N + 1)) :
    commonFactor P ∣ P i :=
  Finset.gcd_dvd (Finset.mem_univ i)

/-- Multiplication by the actual common factor recovers every original coordinate. -/
theorem commonFactor_mul_reduced (P : Fin (N + 1) → k[X])
    (hP : ∃ i, P i ≠ 0) (i : Fin (N + 1)) : commonFactor P * reduced P i = P i :=
  EuclideanDomain.mul_div_cancel' (commonFactor_ne_zero P hP) (commonFactor_dvd P i)

/-- The reduced tuple remains genuinely nonzero. -/
theorem reduced_ne_zero (P : Fin (N + 1) → k[X]) (hP : ∃ i, P i ≠ 0) :
    ∃ i, reduced P i ≠ 0 := by
  obtain ⟨i, hi⟩ := hP
  refine ⟨i, fun hzero ↦ hi ?_⟩
  rw [← commonFactor_mul_reduced P ⟨i, hi⟩ i, hzero, mul_zero]

/-- Dividing the tuple by its finite gcd gives a tuple with gcd exactly one. -/
theorem gcd_reduced_eq_one (P : Fin (N + 1) → k[X]) (hP : ∃ i, P i ≠ 0) :
    Finset.univ.gcd (reduced P) = 1 := by
  apply Finset.extract_gcd' P (reduced P)
  · obtain ⟨i, hi⟩ := hP
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    exact (commonFactor_mul_reduced P hP i).symm

/-- The reduced coordinates satisfy an actual polynomial Bézout identity. -/
theorem exists_bezout_reduced (P : Fin (N + 1) → k[X]) (hP : ∃ i, P i ≠ 0) :
    ∃ B : Fin (N + 1) → k[X], ∑ i, reduced P i * B i = 1 := by
  obtain ⟨B, hB⟩ := Finset.gcd_eq_sum_mul Finset.univ (reduced P)
  refine ⟨B, ?_⟩
  simpa only [gcd_reduced_eq_one P hP] using hB.symm

/-- The maximum degree falls by exactly the degree of the removed common factor. -/
theorem maxDegree_factorization (P : Fin (N + 1) → k[X]) (hP : ∃ i, P i ≠ 0) :
    (commonFactor P).natDegree + maxDegree (reduced P) = maxDegree P := by
  apply le_antisymm
  · obtain ⟨i, hi, hdegree⟩ := exists_nonzero_at_maxDegree (reduced P) (reduced_ne_zero P hP)
    calc
      (commonFactor P).natDegree + maxDegree (reduced P) =
          (commonFactor P * reduced P i).natDegree := by
        rw [Polynomial.natDegree_mul (commonFactor_ne_zero P hP) hi, hdegree]
      _ = (P i).natDegree := congrArg Polynomial.natDegree (commonFactor_mul_reduced P hP i)
      _ ≤ maxDegree P := natDegree_le_maxDegree P i
  · apply maxDegree_le
    intro i
    by_cases hi : reduced P i = 0
    · have hzero : P i = 0 := by rw [← commonFactor_mul_reduced P hP i, hi, mul_zero]
      simp [hzero]
    · rw [← commonFactor_mul_reduced P hP i,
        Polynomial.natDegree_mul (commonFactor_ne_zero P hP) hi]
      exact Nat.add_le_add_left (natDegree_le_maxDegree (reduced P) i) _

/-- Removing the common factor preserves every upper bound on the original coordinate degrees. -/
theorem maxDegree_reduced_le (P : Fin (N + 1) → k[X]) (hP : ∃ i, P i ≠ 0)
    {r : ℕ} (hdegree : ∀ i, (P i).natDegree ≤ r) : maxDegree (reduced P) ≤ r :=
  (Nat.le_add_left _ _).trans ((maxDegree_factorization P hP).le.trans
    (maxDegree_le P hdegree))

/-- The reduced maximum degree has a nonzero coefficient, including when that degree is zero. -/
theorem exists_reduced_topCoefficient_ne_zero (P : Fin (N + 1) → k[X])
    (hP : ∃ i, P i ≠ 0) : ∃ i, (reduced P i).coeff (maxDegree (reduced P)) ≠ 0 :=
  exists_topCoefficient_ne_zero (reduced P) (reduced_ne_zero P hP)

/-- The reduced tuple has no common affine root after any extension of the coefficient field. -/
theorem exists_reduced_eval₂_ne_zero (P : Fin (N + 1) → k[X]) (hP : ∃ i, P i ≠ 0)
    {L : Type v} [Field L] (φ : k →+* L) (t : L) :
    ∃ i, (reduced P i).eval₂ φ t ≠ 0 :=
  exists_eval₂_ne_zero_of_bezout (reduced P) (exists_bezout_reduced P hP) φ t

/-- The reduced homogeneous tuple uses one common degree, the actual reduced maximum. -/
def homogeneousCoordinates (P : Fin (N + 1) → k[X]) (i : Fin (N + 1)) :
    MvPolynomial (Fin 2) k := homog (reduced P i) (maxDegree (reduced P))

/-- Every reduced homogeneous coordinate has the same specified degree. -/
theorem isHomogeneous_homogeneousCoordinates (P : Fin (N + 1) → k[X])
    (i : Fin (N + 1)) : (homogeneousCoordinates P i).IsHomogeneous (maxDegree (reduced P)) :=
  isHomogeneous_homog _ _

/-- The affine chart formula for the actual reduced homogeneous tuple. -/
theorem eval₂_homogeneousCoordinates_one (P : Fin (N + 1) → k[X])
    {L : Type v} [Field L] (φ : k →+* L) (t : L) (i : Fin (N + 1)) :
    MvPolynomial.eval₂ φ ![1, t] (homogeneousCoordinates P i) = (reduced P i).eval₂ φ t :=
  eval₂_homog_one _ (natDegree_le_maxDegree (reduced P) i) φ t

/-- The infinity chart formula for the actual reduced homogeneous tuple. -/
theorem eval₂_homogeneousCoordinates_zero (P : Fin (N + 1) → k[X])
    {L : Type v} [Field L] (φ : k →+* L) (v : L) (i : Fin (N + 1)) :
    MvPolynomial.eval₂ φ ![0, v] (homogeneousCoordinates P i) =
      φ ((reduced P i).coeff (maxDegree (reduced P))) * v ^ maxDegree (reduced P) :=
  eval₂_homog_zero _ _ φ v

/-- No nonzero homogeneous pair is a common zero, over every extension of the base field. -/
theorem exists_homogeneousCoordinates_eval₂_ne_zero (P : Fin (N + 1) → k[X])
    (hP : ∃ i, P i ≠ 0) {L : Type v} [Field L] (φ : k →+* L)
    (u v : L) (huv : u ≠ 0 ∨ v ≠ 0) :
    ∃ i, MvPolynomial.eval₂ φ ![u, v] (homogeneousCoordinates P i) ≠ 0 :=
  exists_homog_eval₂_ne_zero (reduced P) (natDegree_le_maxDegree (reduced P))
    (exists_bezout_reduced P hP) (exists_reduced_topCoefficient_ne_zero P hP) φ u v huv

/-- The original common-degree tuple equals the reduced tuple times the actual common factor
and the padding factor at infinity. This relates affine gcd removal to homogeneous removal. -/
theorem homogenize_original_factorization (P : Fin (N + 1) → k[X])
    (hP : ∃ i, P i ≠ 0) {r : ℕ} (hdegree : ∀ i, (P i).natDegree ≤ r)
    (i : Fin (N + 1)) :
    homog (P i) r =
      MvPolynomial.X 0 ^ (r - ((commonFactor P).natDegree + maxDegree (reduced P))) *
        homog (commonFactor P) (commonFactor P).natDegree * homogeneousCoordinates P i := by
  have hsum : (commonFactor P).natDegree + maxDegree (reduced P) ≤ r :=
    (maxDegree_factorization P hP).le.trans (maxDegree_le P hdegree)
  rw [← commonFactor_mul_reduced P hP i]
  exact homog_mul_padded _ _ le_rfl (natDegree_le_maxDegree (reduced P) i) hsum

end MiyaokaMori.RingTheory.PrimitivePolynomialTuple
