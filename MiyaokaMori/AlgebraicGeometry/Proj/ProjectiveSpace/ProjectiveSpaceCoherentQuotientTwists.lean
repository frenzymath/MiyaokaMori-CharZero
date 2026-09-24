import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverCoherentQuotientTwists

/-! # Coherent sheaves on projective space are quotients of sums of twists

A coherent sheaf `G` on `P^N_k` is a quotient of a finite direct sum of twisting sheaves
(Stacks 01YS (1)): there are `d₁, …, d_r ∈ ℤ` and an epimorphism `⊕_j O(d_j) → G`.

`exists_epi_biproduct_twists_projectiveSpace` is the specialisation `R := k` of
`exists_epi_biproduct_twists_projectiveSpaceOver` (`ProjectiveSpaceOverCoherentQuotientTwists`).
The statements agree definitionally: `ProjectiveSpace N k = ProjectiveSpaceOver N k`
(`ProjectiveSpace_eq_projectiveSpaceOver`) and `projectiveSpaceTwist k N m = projectiveSpaceOverTwist k N m`
(`projectiveSpaceTwist_eq_over`), both `rfl`.

## Route (as formalized in the general module)

`O(1)` is ample on `P^N_R` (`projectiveSpaceOverTwist_one_isAmple`, Stacks 01MW(5) via the cover by
`D_+(T_i)`), and `G` coherent means quasi-coherent of finite type (the two fields of `IsCoherent`).
Stacks 01Q3 (1)⇒(8) (`IsAmple.exists_epi_biproduct_zpow_neg`) gives `n > 0`, `r` and an epimorphism
`⨁_{j<r} O(1)^{⊗-n} ↠ G`, where `O(1)^{⊗-n}` is the ℤ-power `L ^ (-(n:ℤ))` of a line bundle,
i.e. (for `n = m+1`) `moduleTensorPower (dual L) (m+1)`. Finally
`moduleTensorPower (dual O(1)) (m+1) ≅ O(-(m+1))`: pass to the monoidal power `mpow`
(`tensorPowerIsoMpow`) and induct on `m`, using `dual O(1) ≅ O(-1)` (`projectiveSpaceOverTwist_dual`) for
`m = 0` and `O(-1) ⊗ O(-(m+1)) ≅ O(-(m+2))` (`projectiveSpaceOverTwist_tensor`) for the step. Transport
the epimorphism along the resulting isomorphism of biproducts (`biproduct.mapIso`); `d j := -n` for all `j`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 01YS(1)** over a field: a coherent module on `P^N_k` is a quotient of a finite direct sum
of twists `⨁_j O(d_j)`. Specialisation `R := k` of `exists_epi_biproduct_twists_projectiveSpaceOver`. -/
theorem exists_epi_biproduct_twists_projectiveSpace {k : Type u} [Field k] (N : ℕ)
    (G : (ProjectiveSpace N k).Modules) [G.IsCoherent] :
    ∃ (r : ℕ) (d : Fin r → ℤ) (p : CategoryTheory.Limits.biproduct (fun j => projectiveSpaceTwist k N (d j)) ⟶ G),
      CategoryTheory.Epi p :=
  -- `G.IsCoherent` is passed by hand: instance search does not unfold `ProjectiveSpace N k`.
  @exists_epi_biproduct_twists_projectiveSpaceOver k _ N G ‹G.IsCoherent›

end
