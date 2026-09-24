import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedAffineJet
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Homogeneity of the equations of the based affine jet scheme

The coefficient variable indexed by `(i,q)` has weight `q.val + 1`. Substituting the
same universal coordinate series as in `BasedAffineJet` into an arbitrary polynomial
gives a series whose coefficient of order `j` is weighted homogeneous of weight `j`
(`universalEvaluation_coeff_isWeightedHomogeneous`).

No smoothness or field hypothesis is needed. The construction includes order zero
and an empty coordinate set.

Sources: §2 of the paper (the parameter-rescaling grading; eq. (2.7)); and
Ein–Mustață, *Jet Schemes and Singularities*, §2, Proposition 2.2, the affine
construction by coefficients of substituted equations.
-/

noncomputable section

namespace MiyaokaMori.BasedAffineJetGrading

open BasedAffineJet
open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section CoefficientLemmas

variable {R σ : Type*} [CommRing R] {w : σ → ℕ}

private theorem homogeneous_coeff_monomial {a : MvPolynomial σ R} {d : ℕ}
    (ha : a.IsWeightedHomogeneous w d) (q : ℕ) :
    ((Polynomial.monomial d a).coeff q).IsWeightedHomogeneous w q := by
  classical
  by_cases hd : d = q
  · subst q
    simpa only [Polynomial.coeff_monomial_same] using ha
  · rw [Polynomial.coeff_monomial, if_neg hd]
    exact MvPolynomial.isWeightedHomogeneous_zero R w q

private theorem homogeneous_coeff_mul {P Q : Polynomial (MvPolynomial σ R)}
    (hP : ∀ q, (P.coeff q).IsWeightedHomogeneous w q)
    (hQ : ∀ q, (Q.coeff q).IsWeightedHomogeneous w q) (q : ℕ) :
    ((P * Q).coeff q).IsWeightedHomogeneous w q := by
  classical
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ab hab
  simpa only [Finset.mem_antidiagonal.mp hab] using (hP ab.1).mul (hQ ab.2)

end CoefficientLemmas

variable {R : Type*} [CommRing R]

section GeneralCoordinates

variable {n : ℕ}
variable {I : Ideal (MvPolynomial (Fin n) R)} (s : PresentedAlgebra I →ₐ[R] R)

/-- Each coefficient of the universal coordinate series has weight equal to its order. -/
theorem universalCoordinate_coeff_isWeightedHomogeneous (k : ℕ) (i : Fin n) (q : ℕ) :
    ((universalCoordinate s k i).coeff q).IsWeightedHomogeneous
      (fun iq : Fin n × Fin k ↦ iq.2.val + 1) q := by
  classical
  rw [universalCoordinate, Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  apply MvPolynomial.IsWeightedHomogeneous.add
  · exact homogeneous_coeff_monomial
      (MvPolynomial.isWeightedHomogeneous_C _ (baseCoordinate s i)) q
  · apply MvPolynomial.IsWeightedHomogeneous.sum
    intro l _
    exact homogeneous_coeff_monomial
      (MvPolynomial.isWeightedHomogeneous_X R (fun iq : Fin n × Fin k ↦ iq.2.val + 1)
        (i, l)) q

/-- Substitution into the universal based coordinate series sends every coefficient of
order `q` to a weighted homogeneous polynomial of weight `q`. -/
theorem universalEvaluation_coeff_isWeightedHomogeneous (k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    ∀ q : ℕ, ((universalEvaluation s k p).coeff q).IsWeightedHomogeneous
      (fun iq : Fin n × Fin k ↦ iq.2.val + 1) q := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r =>
    intro q
    rw [universalEvaluation, MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
      MvPolynomial.algebraMap_eq]
    exact homogeneous_coeff_monomial (MvPolynomial.isWeightedHomogeneous_C _ r) q
  | add p r hp hr =>
    intro q
    rw [map_add, Polynomial.coeff_add]
    exact (hp q).add (hr q)
  | mul_X p i hp =>
    intro q
    rw [map_mul]
    apply homogeneous_coeff_mul hp
    intro j
    simpa only [universalEvaluation, MvPolynomial.aeval_X] using
      universalCoordinate_coeff_isWeightedHomogeneous s k i j

end GeneralCoordinates

end MiyaokaMori.BasedAffineJetGrading
