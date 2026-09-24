import MiyaokaMori.Prelude
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Rescaling the variables of a weighted-homogeneous polynomial by inverse powers

(Helper for the frame-jet coefficient map, §3 of the paper.)

For `P ∈ R[x_σ]` weighted homogeneous of weight `m` (weights `w : σ → ℕ`), a ring map `g : R → K`
into a field, values `c : σ → K` and a scalar `γ ∈ K`:
`eval₂ g (p ↦ γ^{-w p} · c p) P = γ^{-m} · eval₂ g c P`.
This is the algebraic content of the paper's normalization `a_{α,i,q} = γ^{-q} b_{α,i,q}`: a
weight-`m` function of the coordinates picks up the factor `γ^{-m}`. Valid also for `γ = 0`
(`0^{-n} = 0⁻¹ = 0` for `n > 0`, `0^0 = 1`): the argument uses only `(γ^a)⁻¹ (γ^b)⁻¹ = (γ^{a+b})⁻¹`
and `((γ^a)⁻¹)^d = (γ^{ad})⁻¹`, which hold in any field.

Proof: `IsWeightedHomogeneous.induction_on` (zero, sum, monomial); on a monomial `r x^d` with
`Σ_p d_p w_p = m`, `eval₂_monomial` gives `g r · Π_p (γ^{-w_p} c_p)^{d_p} = g r · (Π_p γ^{-w_p d_p}) ·
Π_p c_p^{d_p}` and `Π_p γ^{-w_p d_p} = γ^{-m}`. -/
set_option autoImplicit false

namespace MvPolynomial

variable {R K σ : Type*} [CommSemiring R] [Field K]

/-- `γ^{-n} = (γ^n)⁻¹` for natural `n`. -/
private theorem zpow_neg_natCast_eq_inv_pow (γ : K) (n : ℕ) : γ ^ (-(n : ℤ)) = (γ ^ n)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

/-- **Rescaling the variables of a weighted-homogeneous polynomial**: for `P` weighted homogeneous
of weight `m`, `eval₂ g (p ↦ γ^{-w p} · c p) P = γ^{-m} · eval₂ g c P`. -/
theorem IsWeightedHomogeneous.eval₂_zpow_neg_weight (w : σ → ℕ) (g : R →+* K) (c : σ → K) (γ : K)
    {P : MvPolynomial σ R} {m : ℕ} (hP : P.IsWeightedHomogeneous w m) :
    MvPolynomial.eval₂ g (fun p => γ ^ (-(w p : ℤ)) * c p) P =
      γ ^ (-(m : ℤ)) * MvPolynomial.eval₂ g c P := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [eval₂_zero, eval₂_zero, mul_zero]
  | add p q _ _ ihp ihq => rw [eval₂_add, eval₂_add, ihp, ihq, mul_add]
  | monomial d r hd =>
    rw [eval₂_monomial, eval₂_monomial, ← hd, Finsupp.weight_apply, Finsupp.sum,
      zpow_neg_natCast_eq_inv_pow]
    simp_rw [Finsupp.prod, zpow_neg_natCast_eq_inv_pow, mul_pow, Finset.prod_mul_distrib, inv_pow,
      ← pow_mul, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
    have hsum : ∑ p ∈ d.support, w p * d p = ∑ p ∈ d.support, d p * w p :=
      Finset.sum_congr rfl fun p _ => mul_comm _ _
    rw [hsum]
    ring

end MvPolynomial
