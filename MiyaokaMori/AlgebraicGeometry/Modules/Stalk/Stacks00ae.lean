import MiyaokaMori.Prelude

/-! # Stalks of the pushforward along a closed embedding (Stacks 00AE)

Stacks 00AE for abelian sheaves: for a closed embedding `i : Z → X` and an abelian sheaf `F` on
`Z`, the stalk `(i_*F)_x` is zero for `x ∉ i(Z)`, and for `x = i(z)` the stalk map
`(i_*F)_{i z} → F_z` is an isomorphism.

Source: Stacks 00AE (`sheaves-lemma-stalks-closed-pushforward`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 00AE, first part: for a closed embedding `i : Z → X` and an abelian sheaf `F` on `Z`,
the stalk of `i_*F` at a point outside `i(Z)` is zero. -/
theorem TopCat.Sheaf.isZero_stalk_pushforward_of_notMem_range {X Z : TopCat.{u}}
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (x : X) (hx : x ∉ Set.range i) :
    CategoryTheory.Limits.IsZero
      (TopCat.Presheaf.stalk ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F).obj x) := by
  let P : TopCat.Presheaf AddCommGrpCat.{u} X :=
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F).obj
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  constructor
  intro a b
  suffices hzero : ∀ t : P.stalk x, t = 0 by
    rw [hzero a, hzero b]
  intro t
  obtain ⟨U, hxU, s, rfl⟩ := P.exists_germ_eq t
  let C : Opens X := ⟨(Set.range i)ᶜ, hi.isClosed_range.isOpen_compl⟩
  let V := U ⊓ C
  have hxC : x ∈ C := hx
  have hxV : x ∈ V := ⟨hxU, hxC⟩
  have hVU : V ≤ U := inf_le_left
  have hpre : (Opens.map i).obj V = ⊥ := by
    ext z
    simp [V, C]
  have hzeroV : IsZero (P.obj (op V)) := by
    change IsZero (F.obj.obj (op ((Opens.map i).obj V)))
    exact (TopCat.Sheaf.isTerminalOfEqEmpty F hpre).isZero
  have hres : P.map (homOfLE hVU).op s = 0 :=
    (AddCommGrpCat.subsingleton_of_isZero hzeroV).elim _ _
  rw [← P.germ_res_apply (homOfLE hVU) x hxV s, hres, map_zero]

/-- Stacks 00AE, second part: for a closed embedding `i : Z → X`, the stalk map
`(i_*F)_{i z} → F_z` (Mathlib's `stalkPushforward`) is an isomorphism. -/
theorem TopCat.Sheaf.isIso_stalkPushforward_of_isClosedEmbedding {X Z : TopCat.{u}}
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (z : Z) :
    CategoryTheory.IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i F.obj z) :=
  TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u} hi.isInducing F.obj z

end
