import MiyaokaMori.Prelude

/-! # Sheaf-cohomology bookkeeping for Grothendieck vanishing (Stacks 02UZ)

Generic facts about `CategoryTheory.Sheaf.H` (= `Ext(ℤ, −)` in the abelian category of abelian
sheaves on a site) used to assemble Stacks 02UZ from its leaves:
* `H` is invariant under isomorphism of sheaves;
* two-out-of-three vanishing along the long exact `Ext` sequence of a short exact sequence
  (Mathlib `Abelian.Ext.covariant_sequence_exact₁/₂`);
* every abelian sheaf on the empty space is zero (the topology on the one open `∅` is `⊤`), so all
  its cohomology vanishes (base case of the induction). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- `H^n` is invariant under isomorphism of sheaves (functoriality of `Sheaf.functorH`). -/
theorem subsingleton_H_of_iso {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ)
    [hF : Subsingleton (H F n)] : Subsingleton (H G n) := by
  have e' := ((functorH J n).mapIso e).addCommGroupIsoToAddEquiv
  have : Subsingleton (((functorH J n).obj F : AddCommGrpCat.{w'}) : Type w') := hF
  exact e'.symm.injective.subsingleton

/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of abelian sheaves, `H^n X₁ = 0` and
`H^n X₃ = 0` imply `H^n X₂ = 0` (exactness of `H^n X₁ → H^n X₂ → H^n X₃`). -/
theorem subsingleton_H_X₂_of_shortExact {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (H S.X₁ n)] [Subsingleton (H S.X₃ n)] : Subsingleton (H S.X₂ n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.covariant_sequence_exact₂ _ hS x (Subsingleton.elim _ _)
  rw [← hx₁, Subsingleton.elim x₁ 0]
  simp

/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of abelian sheaves, `H^{n₀} X₃ = 0` and
`H^{n₀+1} X₂ = 0` imply `H^{n₀+1} X₁ = 0` (exactness of `H^{n₀} X₃ → H^{n₀+1} X₁ → H^{n₀+1} X₂`). -/
theorem subsingleton_H_X₁_of_shortExact {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    [Subsingleton (H S.X₃ n₀)] [Subsingleton (H S.X₂ n₁)] : Subsingleton (H S.X₁ n₁) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) h
  rw [← hx₃, Subsingleton.elim x₃ 0]
  simp

end CategoryTheory.Sheaf

namespace TopCat.Sheaf

/-- On the empty space every abelian sheaf is a zero object: the only open is `∅`, which is covered
by the empty family, so the Grothendieck topology is `⊤` and every sheaf is terminal. -/
theorem isZero_of_isEmpty {T : Type u} [TopologicalSpace T] [IsEmpty T]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) : IsZero F := by
  refine (Sheaf.isTerminalOfEqTop ?_ F).isZero
  refine top_le_iff.mp ?_
  intro U S _ x hx
  exact (IsEmpty.false x).elim

end TopCat.Sheaf

end
