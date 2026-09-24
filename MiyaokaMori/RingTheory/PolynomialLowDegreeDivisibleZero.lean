import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.RingTheory.CoeffZeroAboveDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.PullbackDegreeFiniteCover

/-! # A polynomial of low degree divisible by a high power of `t` vanishes

A purely algebraic fact: a polynomial divisible by `t^(k+1)` and of degree `< k` has all
coefficients zero, hence is identically zero. Used in the polynomial realization
(Theorem 4.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem coeffs_vanish_of_X_pow_succ_dvd {R : Type*} [CommRing R] {f : Polynomial R}
    {κ : ℕ} (hdvd : (Polynomial.X : Polynomial R) ^ (κ + 1) ∣ f)
    (hdeg : f.degree < (κ : WithBot ℕ)) :
    ∀ q : ℕ, f.coeff q = 0 := by
  intro q
  by_cases hq : q < κ + 1
  · rw [Polynomial.X_pow_dvd_iff] at hdvd
    exact hdvd q (by omega)
  · have hqκ : κ ≤ q := by omega
    exact (Polynomial.degree_lt_iff_coeff_zero f κ).1 hdeg q hqκ

end
