import MiyaokaMori.Prelude

/-! # Lifting along a closed immersion from a dense open subset

A morphism from a reduced scheme `X` to `P` which factors through a closed immersion `i : Y → P`
on a dense open subset of `X` factors through `i` globally.

References: Debarre, *Introduction to Mori theory*, first sentence of the proof of Theorem 5.18
("We can replace Y with a projective space"); Hartshorne II, Exercise 3.11(d) (scheme-theoretic
image); [Stacks, 056B].
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- A morphism `Ψ' : X → P` from a reduced scheme which factors through the closed immersion
`i : Y → P` on a dense open `V ⊆ X` factors through `i`.

Proof: use `IsClosedImmersion.lift i Ψ' H` and `IsClosedImmersion.lift_fac`, where
`H : i.ker ≤ Ψ'.ker`. To verify `H`: since `X` is reduced and `V` is dense, `(V.ι).ker = ⊥` (a dense
open immersion into a reduced scheme is scheme-theoretically dominant: for an affine open `U`,
`Γ(U) → Γ(U ∩ V)` is injective because a section of a reduced scheme vanishing on a dense open
subset is zero; in Mathlib, `IsSchemeTheoreticallyDominant.of_isDominant V.ι`, where `IsDominant V.ι`
follows from `hV` via `Opens.isDominant_ι hV`). Hence
`Ψ'.ker = (V.ι ≫ Ψ').ker` (`Scheme.Hom.ker_comp` and `IdealSheafData.map_bot`)
`= (gV ≫ i).ker ≥ i.ker` (`Hom.le_ker_comp`).
Edge case: if `V` is empty then so is `X` (density), and the statement is trivial. -/
theorem AlgebraicGeometry.IsClosedImmersion.exists_lift_of_dense {X Y P : Scheme.{u}} [IsReduced X]
    (i : Y ⟶ P) [IsClosedImmersion i] (Ψ' : X ⟶ P) (V : X.Opens) (hV : Dense (V : Set X))
    (gV : V.toScheme ⟶ Y) (h : V.ι ≫ Ψ' = gV ≫ i) : ∃ Ψ : X ⟶ Y, Ψ ≫ i = Ψ' := by
  have : IsDominant V.ι := Opens.isDominant_ι hV
  have : IsSchemeTheoreticallyDominant V.ι := IsSchemeTheoreticallyDominant.of_isDominant V.ι
  have hker : (V.ι ≫ Ψ').ker = Ψ'.ker := by
    rw [Scheme.Hom.ker_comp, V.ι.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have H : i.ker ≤ Ψ'.ker := by
    rw [← hker, h]
    exact gV.le_ker_comp i
  exact ⟨IsClosedImmersion.lift i Ψ' H, IsClosedImmersion.lift_fac i Ψ' H⟩


end
