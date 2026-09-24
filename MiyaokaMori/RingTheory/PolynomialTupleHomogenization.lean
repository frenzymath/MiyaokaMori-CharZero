import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Common-degree homogenization of polynomial tuples in the `[1:t]` convention

The project uses affine coordinate `[1:t]` and zero `[1:0]`. Mathlib's univariate
homogenization uses `[t:1]`, so `homog` renames its two variables by their swap. Its
dehomogenization, infinity value, multiplication, and padding identities retain this same
choice of coordinates.

A tuple with a genuine polynomial Bézout identity and a nonzero coefficient in its common
top degree has no common homogeneous zero after any extension of the coefficient field.
Consumers must derive those two hypotheses for their actual tuple. This file does not
construct its gcd or quotient tuple, a projective morphism, or a pullback line bundle degree.
In particular, no homogeneous-polynomial degree is identified here with geometric degree.

Sources: the proof of Theorem 4.2 of the paper; Stacks `algebra.tex`, `lemma-homogenize`
(homogeneous padding in the `X₀=1` chart); `curves.tex`, `lemma-linear-series`
(the subsequent geometric construction, which is not carried out here).
Initial generic proof drafts were supplied by `/root/e_generic_nonscalar`; the unique writer
of this canonical module is `/root/e_frame_compatibility`.
-/

noncomputable section

namespace MiyaokaMori.RingTheory.PolynomialTupleHomogenization

open Polynomial
open scoped BigOperators

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Common-degree homogenization with affine coordinate `[1:t]` and zero `[1:0]`. -/
def homog (p : R[X]) (d : ℕ) : MvPolynomial (Fin 2) R :=
  MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (p.homogenize d)

/-- Swapping variables preserves the homogeneous degree. -/
theorem isHomogeneous_homog (p : R[X]) (d : ℕ) : (homog p d).IsHomogeneous d :=
  (Polynomial.isHomogeneous_homogenize p).rename_isHomogeneous

/-- Evaluating our homogenization swaps the two evaluation coordinates in Mathlib's model. -/
theorem eval₂_homog (p : R[X]) (d : ℕ) (φ : R →+* S) (u v : S) :
    MvPolynomial.eval₂ φ ![u, v] (homog p d) =
      MvPolynomial.eval₂ φ ![v, u] (p.homogenize d) := by
  rw [homog, MvPolynomial.eval₂_rename]
  have hswap : (![u, v] : Fin 2 → S) ∘ Equiv.swap (0 : Fin 2) 1 = ![v, u] := by
    funext i
    fin_cases i <;> simp
  rw [hswap]

/-- On `[1:t]`, homogenization recovers the actual polynomial when the degree bound holds.
The bound is explicit because homogenization to a smaller degree would discard terms. -/
theorem eval₂_homog_one (p : R[X]) {d : ℕ} (hdegree : p.natDegree ≤ d)
    (φ : R →+* S) (t : S) :
    MvPolynomial.eval₂ φ ![1, t] (homog p d) = p.eval₂ φ t := by
  rw [eval₂_homog]
  exact Polynomial.eval₂_homogenize_of_eq_one hdegree φ ![t, 1] (by simp)

/-- At `[0:v]`, the value is the degree-`d` coefficient times `v^d`. This formula holds for
every `d`; a degree bound is required separately whenever recovering the whole polynomial. -/
theorem eval₂_homog_zero (p : R[X]) (d : ℕ) (φ : R →+* S) (v : S) :
    MvPolynomial.eval₂ φ ![0, v] (homog p d) = φ (p.coeff d) * v ^ d := by
  rw [eval₂_homog, Polynomial.homogenize, MvPolynomial.eval₂_sum]
  rw [Finset.sum_eq_single (d, 0)]
  · simp [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  · intro a ha hne
    have ha_sum : a.1 + a.2 = d := Finset.mem_antidiagonal.mp ha
    have ha₂ : a.2 ≠ 0 := by
      intro hz
      apply hne
      exact Prod.ext (by simpa [hz] using ha_sum) hz
    simp [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, ha₂]
  · simp

/-- Homogenization respects multiplication when both input degrees are bounded. -/
theorem homog_mul (p q : R[X]) {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    homog (p * q) (m + n) = homog p m * homog q n := by
  simp only [homog, Polynomial.homogenize_mul p q hp hq, map_mul]

/-- Increasing the homogeneous degree pads by a power of `X₀`, the infinity factor. -/
theorem homog_add_degree (p : R[X]) {d : ℕ} (hdegree : p.natDegree ≤ d) (e : ℕ) :
    homog p (e + d) = MvPolynomial.X 0 ^ e * homog p d := by
  have hmul := homog_mul (1 : R[X]) p (m := e) (n := d) (by simp) hdegree
  simpa [homog, Polynomial.homogenize_one] using hmul

/-- Padding to any larger specified degree uses the actual difference of degrees. -/
theorem homog_of_le_degree (p : R[X]) {d r : ℕ}
    (hdegree : p.natDegree ≤ d) (hdr : d ≤ r) :
    homog p r = MvPolynomial.X 0 ^ (r - d) * homog p d := by
  simpa only [Nat.sub_add_cancel hdr] using homog_add_degree p hdegree (r - d)

/-- A product homogenized to a larger common degree is the product of its two bounded
homogenizations and the necessary `X₀` padding. This is a polynomial identity, including
zero factors; it makes no assertion about geometric cancellation on projective space. -/
theorem homog_mul_padded (p q : R[X]) {m n r : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) (hmnr : m + n ≤ r) :
    homog (p * q) r =
      MvPolynomial.X 0 ^ (r - (m + n)) * homog p m * homog q n := by
  rw [homog_of_le_degree (p * q) (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq))
    hmnr, homog_mul p q hp hq, mul_assoc]

end CommSemiring

section Fields

variable {k L : Type*} [Field k] [Field L]

/-- On the chart `u ≠ 0`, homogenization is the affine value at `v/u`, multiplied by `u^d`.
The coefficient homomorphism may be any field homomorphism into any extension field. -/
theorem eval₂_homog_of_ne_zero (p : k[X]) {d : ℕ} (hdegree : p.natDegree ≤ d)
    (φ : k →+* L) (u v : L) (hu : u ≠ 0) :
    MvPolynomial.eval₂ φ ![u, v] (homog p d) = p.eval₂ φ (v / u) * u ^ d := by
  rw [eval₂_homog, MvPolynomial.eval₂_eq_eval_map, ← Polynomial.homogenize_map]
  rw [Polynomial.eval_homogenize (Polynomial.natDegree_map_le.trans hdegree) _ (by simpa)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Polynomial.eval_map]

/-- An actual finite polynomial Bézout identity excludes a common affine root over every
extension field. The identity is data to be proved for the caller's actual tuple. -/
theorem exists_eval₂_ne_zero_of_bezout {N : ℕ} (Q : Fin (N + 1) → k[X])
    (hbezout : ∃ B : Fin (N + 1) → k[X], ∑ i, Q i * B i = 1)
    (φ : k →+* L) (t : L) : ∃ i, (Q i).eval₂ φ t ≠ 0 := by
  classical
  by_contra! hzero
  obtain ⟨B, hB⟩ := hbezout
  have heval := congrArg (Polynomial.eval₂RingHom φ t) hB
  simp only [map_sum, map_mul, Polynomial.coe_eval₂RingHom, hzero, zero_mul,
    Finset.sum_const_zero, map_one] at heval
  exact zero_ne_one heval

/-- A bounded tuple with an actual Bézout identity and a nonzero top coefficient has no
common homogeneous zero over any extension field. Neither `d > 0` nor nonzero individual
coordinates are assumed; the conclusion covers the constant-degree case as well. -/
theorem exists_homog_eval₂_ne_zero {N d : ℕ} (Q : Fin (N + 1) → k[X])
    (hdegree : ∀ i, (Q i).natDegree ≤ d)
    (hbezout : ∃ B : Fin (N + 1) → k[X], ∑ i, Q i * B i = 1)
    (htop : ∃ j, (Q j).coeff d ≠ 0) (φ : k →+* L)
    (u v : L) (huv : u ≠ 0 ∨ v ≠ 0) :
    ∃ i, MvPolynomial.eval₂ φ ![u, v] (homog (Q i) d) ≠ 0 := by
  by_cases hu : u = 0
  · subst u
    have hv : v ≠ 0 := huv.resolve_left (not_ne_iff.mpr rfl)
    obtain ⟨i, hi⟩ := htop
    refine ⟨i, ?_⟩
    rw [eval₂_homog_zero]
    exact mul_ne_zero (by simpa only [map_zero] using φ.injective.ne hi) (pow_ne_zero _ hv)
  · obtain ⟨i, hi⟩ := exists_eval₂_ne_zero_of_bezout Q hbezout φ (v / u)
    refine ⟨i, ?_⟩
    rw [eval₂_homog_of_ne_zero _ (hdegree i) φ u v hu]
    exact mul_ne_zero hi (pow_ne_zero _ hu)

end Fields

end MiyaokaMori.RingTheory.PolynomialTupleHomogenization
