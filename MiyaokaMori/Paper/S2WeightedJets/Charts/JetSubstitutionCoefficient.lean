import MiyaokaMori.Prelude

/-! # Coefficients of a substituted jet

The coefficient of `t^q` after substituting the truncated coefficient series
`x_i(t) = Σ_{q=1}^{k} x_{i,q} t^q` into a formal coordinate change `Φ(X_i)`, as a polynomial in the
coordinates `x_{α,i,q}` (eq. (2.7) of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The origin section `s₀ : R[x_0, …, x_n]/⊥ → R` (evaluation at `0`); the constant term of the
universal coordinate `universalCoordinate s₀ k` is therefore `0`. -/
noncomputable def jetOriginSection {R : Type u} [CommRing R] (n : ℕ) :
    MiyaokaMori.BasedAffineJet.PresentedAlgebra (⊥ : Ideal (MvPolynomial (Fin (n + 1)) R)) →ₐ[R] R :=
  Ideal.Quotient.liftₐ ⊥ (MvPolynomial.aeval (fun _ => (0 : R)))
    (fun a ha => by rw [Ideal.mem_bot] at ha; rw [ha, map_zero])

/-- The coefficient of `t^q` in `Φ(X_i)(x(t))`, where `x_i(t) = Σ_{q'<k} X_{(i,q')} t^{q'+1}`:
`MiyaokaMori.BasedAffineJet.universalEvaluation s₀ k` (substitution of the `x_j(t)` into a polynomial)
is applied to the truncation of `Φ(X_i)` to exponents `≤ q` in every variable (`trunc'`), and the
coefficient of `t^q` is taken. The discarded monomials have total degree `> q`, and each `x_j(t)`
is divisible by `t`, so they do not contribute to the coefficient of `t^q`; hence for every `q`
this agrees with substituting into the whole power series. -/
noncomputable def jetSubstitutionCoeff {R : Type u} [CommRing R] (n k : ℕ)
    (Φ : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] MvPowerSeries (Fin (n + 1)) R)
    (i : Fin (n + 1)) (q : ℕ) : MvPolynomial (Fin (n + 1) × Fin k) R :=
  (MiyaokaMori.BasedAffineJet.universalEvaluation (jetOriginSection n) k
    (MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm (fun _ => q)) (Φ (MvPowerSeries.X i)))).coeff q

end
