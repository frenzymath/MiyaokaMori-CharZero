import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.MvPolynomial.Coeff

/-! # The diagonal coefficient of a numerical polynomial

A combinatorial identity: if `P ∈ ℚ[x]` has degree `≤ d`, then the coefficient of the monomial
`n₁ ⋯ n_d` in the `d`-variable polynomial `P(n₁ + ⋯ + n_d)` equals `d! · (coefficient of x^d in P)`.
This is used in the computation of the weighted intersection number (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem Polynomial.coeff_prod_X_comp_sum_X {d : ℕ} (P : Polynomial ℚ) (hP : P.natDegree ≤ d) :
    MvPolynomial.coeff (∑ i : Fin d, Finsupp.single i 1)
        (Polynomial.aeval (∑ i : Fin d, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) P)
      = (Nat.factorial d : ℚ) * P.coeff d := by
  classical
  let m : Fin d →₀ ℕ := ∑ i : Fin d, Finsupp.single i 1
  have hm_apply (i : Fin d) : m i = 1 := by simp [m]
  have hm_support : m.support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, hm_apply i]
  have hm_sum : m.sum (fun _ n => n) = d := by
    rw [Finsupp.sum, hm_support]
    simp [hm_apply]
  have hm_sum_id : m.sum (fun _ => id) = d := by
    rw [Finsupp.sum, hm_support]
    simp [hm_apply]
  have hm_mult : m.multinomial = Nat.factorial d := by
    rw [Finsupp.multinomial, hm_sum_id, Finsupp.prod, hm_support]
    simp [hm_apply]
  change MvPolynomial.coeff m
      (Polynomial.aeval (∑ i : Fin d, MvPolynomial.X i : MvPolynomial (Fin d) ℚ) P) = _
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum]
  rw [Polynomial.sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sum_X_pow_of_fintype, hm_sum, hm_mult]
  by_cases hd : P.coeff d = 0
  · simp [hd]
  · simp [Polynomial.mem_support_iff, hd, mul_comm]

end
