import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansion
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalarOfCoefficientsZero

/-! # The coefficient sections of a based jet

Pulling back the `ℓ`-th cone coordinate along `ȷ` gives `P_ℓ^(k) = ρ^*f_ℓ + Σ_{q=1}^{k} c_{ℓ,q} ξ^q` with
`c_{ℓ,q} ∈ H^0(C̃, ρ^*A ⊗ L^{-q})`; if `ȷ` is not generically scalar, some `c_{ℓ,q} ≠ 0`
(equation (4.1), Lemma 4.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Equation (4.1): `P_ℓ = ρ^*f_ℓ + Σ_{q=1}^{κ} c_{ℓ,q} ξ^q`, where `c_{ℓ,q} = J.coefficient ℓ q`
and `c · ξ^q` is the monomial `xiMonomial` (a section of `p^*ρ^*A` on `Tot(L)`) restricted to `C̃_(κ)(L)`. -/
theorem jet_coefficient_expansion {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (ℓ : Fin (X.embDim + 1)) :
    BasedJet.coneCoordinate J ℓ
      = restrictToThickening L (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ
          (sectionPullbackAlong
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
            (sectionPullbackAlong ρ.hom
            ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
              (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom (D.coord ℓ))))
        + ∑ q : Fin κ,
            restrictToThickening L (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ
              (xiMonomial L (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) ((q : ℕ) + 1) (BasedJet.coefficient J ℓ ((q : ℕ) + 1))) := by
  exact BasedJet.coneCoordinate_finite_xi_expansion J ℓ

/-- If `J` is not generically scalar, some positive-order coefficient `c_{ℓ,q}` is nonzero. -/
theorem jet_coefficient_ne_zero_of_not_scalar {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hns : ¬ J.IsGenericallyScalar) :
    ∃ (ℓ : Fin (X.embDim + 1)) (q : Fin κ),
      BasedJet.coefficient J ℓ ((q : ℕ) + 1) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_ne_iff] at h
  exact hns (J.isGenericallyScalar_of_coefficients_eq_zero h)

end
