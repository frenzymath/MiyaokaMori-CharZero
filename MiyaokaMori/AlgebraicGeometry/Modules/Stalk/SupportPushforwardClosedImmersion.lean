import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.Stacks00ae
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics

/-! # Support of the pushforward along a closed immersion

Stacks 00AE for supports: for a closed immersion `i : Z → X` and `M : Z.Modules`,
`Supp (i_* M) = i(Supp M)`. Off the image the stalks of `i_* M` vanish
(`Stacks00ae.isZero_stalk_pushforward_of_notMem_range`); at `i z` the stalk of `i_* M` is the stalk of `M`
at `z` (Mathlib `stalkPushforward_iso_of_isInducing`). Used in the dévissage over a Noetherian
scheme (with `Supp M = Z`, so that `Supp (i_* M) = i(Z) = closure {ξ}`).

Source: Stacks 00AE (sheaves-lemma-stalks-closed-pushforward).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Stacks 00AE for supports**: `Supp (i_* M) = i '' Supp M` for a closed immersion `i`. The inclusion
`⊇` is `Stacks0bemSupport.mem_support_pushforward_of_isClosedImmersion`; for `⊆`, a point outside the
image has zero stalk (00AE), and at `i z` the stalk of `i_* M` is isomorphic to `M_z`. -/
theorem support_pushforward_of_isClosedImmersion
    {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (M : Z.Modules) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).support = i.base '' M.support := by
  ext x
  constructor
  · intro hx
    rw [mem_support_iff] at hx
    by_cases hr : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hr
      refine ⟨z, ?_, rfl⟩
      rw [mem_support_iff]
      have hiso : IsIso (M.presheaf.stalkPushforward AddCommGrpCat.{u} i.base z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
          i.isClosedEmbedding.isInducing M.presheaf z
      have hbij := ConcreteCategory.bijective_of_isIso
        (M.presheaf.stalkPushforward AddCommGrpCat.{u} i.base z)
      have h1 : Nontrivial ((i.base _* M.presheaf).stalk (i.base z)) := hx
      exact (Equiv.ofBijective _ hbij).symm.nontrivial
    · exfalso
      have hz := TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range i.base i.isClosedEmbedding
        ⟨M.presheaf, M.isSheaf⟩ x hr
      have h1 : Nontrivial ((i.base _* M.presheaf).stalk x) := hx
      have h2 : Subsingleton ((i.base _* M.presheaf).stalk x) :=
        AddCommGrpCat.subsingleton_of_isZero hz
      exact not_nontrivial_iff_subsingleton.mpr h2 h1
  · rintro ⟨z, hz, rfl⟩
    exact mem_support_pushforward_of_isClosedImmersion i M hz

end AlgebraicGeometry.Scheme.Modules

end
