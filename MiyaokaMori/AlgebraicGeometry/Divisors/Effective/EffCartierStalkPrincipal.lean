import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm

/-! # Stalks of the ideal sheaf of an effective Cartier divisor

The ideal sheaf of an effective Cartier divisor is generated on every stalk by one nonzerodivisor
(Stacks 01WS; Hartshorne II, definition before Proposition 6.13).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For an effective Cartier divisor `D` on an integral scheme `X`, `(I_D)_x = (d)` with `d ≠ 0` (the
stalk is a domain, so `d` is a nonzerodivisor).

Proof: `D.exists_localEquation x` gives an affine open `U ∋ x` and a nonzerodivisor `a ∈ Γ(U)` with
`I_D(U) = (a)`. Let `d := germ_x a`. By `stalkIdeal_eq_map_germ`, `Ideal.map_span` and
`Set.image_singleton`, `(I_D)_x = (d)`. Since `a ≠ 0` (a nonzerodivisor in the nontrivial ring `Γ(U)`)
and the germ map is injective (`AlgebraicGeometry.germ_injective_of_isIntegral`), `d ≠ 0`. -/
theorem AlgebraicGeometry.EffectiveCartierDivisor.exists_stalkIdeal_eq_span_singleton
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (D : AlgebraicGeometry.EffectiveCartierDivisor X) (x : X) :
    ∃ d : X.presheaf.stalk x, d ≠ 0 ∧ D.idealSheaf.stalkIdeal x = Ideal.span {d} := by
  obtain ⟨U, hxU, a, ha, hI⟩ := AlgebraicGeometry.Scheme.EffCartier.exists_localEquation D x
  refine ⟨X.presheaf.germ U.1 x hxU a, ?_, ?_⟩
  · intro h0
    have hinj := AlgebraicGeometry.germ_injective_of_isIntegral (X := X) (U := U.1) x hxU
    have hnt : Nontrivial Γ(X, U.1) := (X.presheaf.germ U.1 x hxU).hom.domain_nontrivial
    have ha0 : a = 0 := hinj (by rw [h0, map_zero])
    exact nonZeroDivisors.ne_zero ha ha0
  · rw [AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_map_germ D.idealSheaf x U hxU, hI,
      Ideal.map_span, Set.image_singleton]

end
