import MiyaokaMori.Prelude

/-! # Pushforward along a closed embedding preserves epimorphisms

If `i : Z → X` is a closed embedding of topological spaces, then the pushforward of abelian sheaves
`i_* : Ab(Z) → Ab(X)` preserves epimorphisms.

Proof (without stalks, using "epi = locally surjective" for sheaves):
1. In the sheaf category, epimorphisms are the locally surjective morphisms (Mathlib
   `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`, valid for sheaves valued in `AddCommGrpCat`:
   `HasSheafify`, `WEqualsLocallyBijective`, `Balanced` all have instances).
2. Let `α : F ⟶ G` be locally surjective. Take an open `U` of `X` and `s ∈ (i_*G)(U) = G(i⁻¹U)`. For the
   Grothendieck topology of the space `X`, a sieve covers `U` iff every point of `U` lies in some open of the
   sieve (`Opens.mem_grothendieckTopology`). So it suffices to find, for every `x ∈ U`, an open
   neighbourhood `V ≤ U` of `x` with `s|V` in the image of `(i_*α)(V) = α(i⁻¹V)`.
3. If `x ∈ i(Z)`: write `x = i z`, so `z ∈ i⁻¹U`. Local surjectivity of `α` gives an open `W ≤ i⁻¹U` of `Z`
   with `z ∈ W` and `s|W` in the image of `α(W)`. Since `i` is an embedding, `W = i⁻¹W'` for an open `W'` of
   `X`. Take `V := U ⊓ W'`: `x ∈ V`, and `i⁻¹V = i⁻¹U ⊓ W ≤ W`, so `s|V` is in the image by downward
   closure of the sieve.
4. If `x ∉ i(Z)` (**this is where closedness is used**): `i(Z)` is closed, so `V := U ⊓ i(Z)ᶜ` is an open
   neighbourhood of `x` with `i⁻¹V = ∅`. The value of a sheaf on `∅` is terminal
   (`TopCat.Sheaf.isTerminalOfEqEmpty`), i.e. the zero group in `AddCommGrpCat`, whose carrier is a
   subsingleton, so `s|V` is trivially in the image (preimage `0`).

Source: Stacks 01AX (which uses stalks; here local surjectivity is used instead, avoiding the comparison of
stalks).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X Z : TopCat.{u}}

/-- Pushforward along a closed embedding preserves local surjectivity of morphisms of abelian sheaves. -/
theorem pushforward_isLocallySurjective_of_isClosedEmbedding
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} Z} (α : F ⟶ G)
    [CategoryTheory.Sheaf.IsLocallySurjective α] :
    CategoryTheory.Sheaf.IsLocallySurjective
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map α) := by
  constructor
  intro U s x hx
  by_cases hxZ : x ∈ Set.range (i : Z → X)
  · obtain ⟨z, rfl⟩ := hxZ
    have hz : z ∈ (Opens.map i).obj U := hx
    obtain ⟨W, hWle, hW, hzW⟩ :=
      CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology Z) α.hom
        (U := op ((Opens.map i).obj U)) s z hz
    obtain ⟨W', hW'open, hW'⟩ := hi.isInducing.isOpen_iff.1 W.2
    refine ⟨U ⊓ ⟨W', hW'open⟩, homOfLE inf_le_left, ?_, hx, ?_⟩
    · have hle : (Opens.map i).obj (U ⊓ ⟨W', hW'open⟩) ≤ W := by
        intro y hy
        have : y ∈ (i : Z → X) ⁻¹' W' := hy.2
        rw [hW'] at this
        exact this
      exact (CategoryTheory.Presheaf.imageSieve α.hom s).downward_closed hW (homOfLE hle)
    · exact hW'.ge hzW
  · set Vc : Opens X := ⟨(Set.range (i : Z → X))ᶜ, hi.isClosed_range.isOpen_compl⟩ with hVcdef
    refine ⟨U ⊓ Vc, homOfLE inf_le_left, ?_, hx, hxZ⟩
    have hbot : (Opens.map i).obj (U ⊓ Vc) = ⊥ := by
      apply Opens.ext
      apply Set.eq_empty_iff_forall_notMem.2
      rintro y ⟨-, hy⟩
      exact hy (Set.mem_range_self y)
    have hterm := G.isTerminalOfEqEmpty hbot
    have hzero : Limits.IsZero (G.obj.obj (op ((Opens.map i).obj (U ⊓ Vc)))) :=
      Limits.IsZero.of_iso (Limits.isZero_zero AddCommGrpCat.{u})
        (hterm.uniqueUpToIso (Limits.isZero_zero AddCommGrpCat.{u}).isTerminal)
    have hsub := AddCommGrpCat.subsingleton_of_isZero hzero
    exact ⟨0, @Subsingleton.elim _ hsub _ _⟩

/-- **Pushforward along a closed embedding preserves epimorphisms of abelian sheaves** (Stacks 01AX). -/
theorem pushforward_preservesEpimorphisms_of_isClosedEmbedding
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).PreservesEpimorphisms where
  preserves {F G} α hα := by
    have hls : CategoryTheory.Sheaf.IsLocallySurjective α :=
      (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' _ α).2 hα
    have := pushforward_isLocallySurjective_of_isClosedEmbedding i hi α
    exact (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' _ _).1 this

end TopCat.Sheaf

end
