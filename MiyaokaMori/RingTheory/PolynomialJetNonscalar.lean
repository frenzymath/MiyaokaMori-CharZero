import MiyaokaMori.RingTheory.TruncatedJetRing
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

/-!
# Nonscalar truncated tuples give nonconstant rational coordinate ratios

This is the local function-field step in the proof of Theorem 4.2 of the paper. A polynomial
tuple with a nonzero value at zero is a single scalar polynomial times that value if its
cross-products with that value vanish. The scalar has value one at zero, so its image in
the canonical truncated polynomial ring is a unit. Contrapositively, a nonscalar truncated
tuple has a nonzero cross-product. One of its coordinate ratios in the actual fraction
field of the polynomial ring therefore lies outside the constant field.

There is no hypothesis that the first-order coefficient is nonzero, no infinitude or
characteristic hypothesis on the field, and no degree bound. This file does not construct
the projective scheme morphism, prove that it is nonconstant as a scheme morphism, or
spread the generic conclusion to an open set of ruling fibers.
-/

noncomputable section

namespace MiyaokaMori.Jet

open Polynomial

/-- A polynomial equal to one at zero has invertible image in the actual truncated ring.
The proof uses nilpotence of the parameter, and works over any commutative ring. -/
theorem isUnit_jetProjection_of_eval_zero_eq_one {R : Type*} [CommRing R]
    (T : ℕ) (p : R[X]) (hp : p.eval 0 = 1) : IsUnit (jetProjection R T p) := by
  have hdvd : (X : R[X]) ∣ p - 1 := by
    apply Polynomial.X_dvd_iff.mpr
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [hp]
  obtain ⟨q, hq⟩ := hdvd
  have hnil : IsNilpotent (jetProjection R T (p - 1)) := by
    refine ⟨T + 1, ?_⟩
    rw [hq, map_mul, mul_pow]
    have hparameter : (jetProjection R T (X : R[X])) ^ (T + 1) = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton _))
    rw [hparameter, zero_mul]
  simpa only [map_sub, map_one, sub_add_cancel] using hnil.isUnit_add_one

variable {K ι : Type*} [Field K]

/-- Vanishing of the seed minors with any fixed nonzero seed coordinate gives one common
scalar polynomial, whose value at zero is one. The coordinate index need not be finite. -/
theorem exists_scalar_polynomial_of_minors_zero (P : ι → K[X]) (a : ι → K)
    (hseed : ∀ i, (P i).eval 0 = a i) (j : ι) (hj : a j ≠ 0)
    (hminor : ∀ i, P i * C (a j) - P j * C (a i) = 0) :
    ∃ p : K[X], p.eval 0 = 1 ∧ ∀ i, P i = p * C (a i) := by
  refine ⟨P j * C ((a j)⁻¹), ?_, ?_⟩
  · simp [hseed, hj]
  · intro i
    calc
      P i = (P i * C (a j)) * C ((a j)⁻¹) := by
        simp [mul_assoc, ← C_mul, hj]
      _ = (P j * C (a i)) * C ((a j)⁻¹) := by rw [sub_eq_zero.mp (hminor i)]
      _ = (P j * C ((a j)⁻¹)) * C (a i) := by ac_rfl

/-- The common scalar descends to an invertible scalar of the very same truncated tuple.
Its polynomial representative records the required normalization at zero explicitly. -/
theorem exists_scalar_jet_of_minors_zero (T : ℕ) (P : ι → K[X]) (a : ι → K)
    (hseed : ∀ i, (P i).eval 0 = a i) (j : ι) (hj : a j ≠ 0)
    (hminor : ∀ i, P i * C (a j) - P j * C (a i) = 0) :
    ∃ p : K[X], p.eval 0 = 1 ∧ IsUnit (jetProjection K T p) ∧
      ∀ i, jetProjection K T (P i) =
        jetProjection K T p * jetProjection K T (C (a i)) := by
  obtain ⟨p, hp, hP⟩ := exists_scalar_polynomial_of_minors_zero P a hseed j hj hminor
  refine ⟨p, hp, isUnit_jetProjection_of_eval_zero_eq_one T p hp, ?_⟩
  intro i
  rw [hP i, map_mul]

/-- If the truncated tuple is not a unit multiple of the seed, one of the seed minors
with any nonzero seed coordinate is nonzero. No first-order coefficient is singled out. -/
theorem exists_nonzero_minor_of_nonscalar_jet (T : ℕ) (P : ι → K[X]) (a : ι → K)
    (hseed : ∀ i, (P i).eval 0 = a i) (j : ι) (hj : a j ≠ 0)
    (hnonscalar : ¬ ∃ u : (TruncatedJetRing K T)ˣ,
      ∀ i, jetProjection K T (P i) = (u : TruncatedJetRing K T) *
        jetProjection K T (C (a i))) :
    ∃ i, P i * C (a j) - P j * C (a i) ≠ 0 := by
  classical
  by_contra h
  have hminor : ∀ i, P i * C (a j) - P j * C (a i) = 0 := by simpa using h
  obtain ⟨p, hp, hunit, htuple⟩ := exists_scalar_jet_of_minors_zero T P a hseed j hj hminor
  obtain ⟨u, hu⟩ := hunit
  apply hnonscalar
  refine ⟨u, ?_⟩
  intro i
  simpa only [hu] using htuple i

/-- A nonzero seed minor detects a coordinate ratio outside the constant field in the
actual fraction field `Frac(K[X])`. The nonzero seed coordinate supplies a nonzero
denominator, including when the other seed coordinate vanishes. -/
theorem coordinate_ratio_ne_constant_of_nonzero_minor (P : ι → K[X]) (a : ι → K)
    (hseed : ∀ i, (P i).eval 0 = a i) (i j : ι) (hj : a j ≠ 0)
    (hminor : P i * C (a j) - P j * C (a i) ≠ 0) (c : K) :
    algebraMap K[X] (FractionRing K[X]) (P i) /
        algebraMap K[X] (FractionRing K[X]) (P j) ≠
      algebraMap K[X] (FractionRing K[X]) (C c) := by
  have hPj : P j ≠ 0 := by
    intro hzero
    apply hj
    rw [← hseed j, hzero, Polynomial.eval_zero]
  have hdenom : algebraMap K[X] (FractionRing K[X]) (P j) ≠ 0 := by
    intro hzero
    apply hPj
    exact (IsFractionRing.injective K[X] (FractionRing K[X])) (by simpa using hzero)
  intro hratio
  have hmul := (div_eq_iff hdenom).mp hratio
  have hpoly : P i = C c * P j := by
    apply IsFractionRing.injective K[X] (FractionRing K[X])
    simpa only [map_mul] using hmul
  have hconstant : a i = c * a j := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, hseed] using
      congrArg (Polynomial.eval (0 : K)) hpoly
  apply hminor
  rw [hpoly, hconstant, C_mul]
  ring

/-- A nonscalar jet based at a nonzero tuple gives a rational coordinate ratio that is
not any constant. This is the algebraic generic-fiber input to projectivization. -/
theorem exists_nonconstant_coordinate_ratio_of_nonscalar_jet
    (T : ℕ) (P : ι → K[X]) (a : ι → K) (hseed : ∀ i, (P i).eval 0 = a i)
    (j : ι) (hj : a j ≠ 0)
    (hnonscalar : ¬ ∃ u : (TruncatedJetRing K T)ˣ,
      ∀ i, jetProjection K T (P i) = (u : TruncatedJetRing K T) *
        jetProjection K T (C (a i))) :
    ∃ i, ∀ c : K, algebraMap K[X] (FractionRing K[X]) (P i) /
        algebraMap K[X] (FractionRing K[X]) (P j) ≠
      algebraMap K[X] (FractionRing K[X]) (C c) := by
  obtain ⟨i, hi⟩ := exists_nonzero_minor_of_nonscalar_jet T P a hseed j hj hnonscalar
  exact ⟨i, coordinate_ratio_ne_constant_of_nonzero_minor P a hseed i j hj hi⟩

end MiyaokaMori.Jet
