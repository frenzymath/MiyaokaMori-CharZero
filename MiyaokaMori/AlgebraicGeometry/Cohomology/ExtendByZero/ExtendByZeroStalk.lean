import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.TopcatSheafOpenClosedFunctors
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uzExtendByZero

/-! # Stalks of the extension by zero

Stalks of the extension by zero `j_!` (Stacks 00A5 (3)(5)): for `j : U ↪ X` open and `G` an abelian sheaf
on `U`, `j_!G = extendByZero U G`; `(j_!G)_x ≅ G_x` for `x ∈ U`, `(j_!G)_x = 0` for `x ∉ U`, and
`(j_!G)|_U ≅ G`.

Source: Stacks 00A5 (sheaves-lemma-j-shriek-abelian) (3)(5).

## Route

Write `P := extendByZeroPresheaf U G` (`P(V) = G(V)` if `V ⊆ U`, else `0`; `Stacks02uzExtendByZero.lean`),
so that `extendByZero U G = sheafify P` by `rfl` (`extendByZero_eq_sheafify`), and let
`ι : P ⟶ j_* G` be the inclusion `extendByZeroPresheafι` (injective on every open).
* Stacks 007Z (stalks of a presheaf and of its sheafification agree) is Mathlib's
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`: the stalk map of `toSheafify P` is an iso.
* `x ∉ U`: every germ of `P` at `x` is the germ of a section over some `V ∋ x`; `V ⊄ U`, so `P(V) = 0`
  and the germ is `0`; hence `P_x = 0` (`isZero_extendByZeroPresheaf_stalk_of_notMem`).
* `x ∈ U`: the stalk map `P_x ⟶ (j_* G)_x` of `ι` is injective (Mathlib
  `stalkFunctor_map_injective_of_app_injective`) and surjective (a germ of `j_* G` at `x` is represented
  over some `V ⊆ U`, by `exists_le_germ_eq`, and there `P(V) = (j_* G)(V)`), so an iso
  (`isIso_stalkFunctor_map_extendByZeroPresheafι`); and `(j_* G)_x ≅ G_x` for the open embedding `j`
  (Mathlib `stalkPushforward.stalkPushforward_iso_of_isInducing`).
* `(j_! G)|_U ≅ G`: the sheaf map `ι' : j_! G ⟶ j_* G` (`extendByZeroToPushforward`) satisfies
  `toSheafify P ≫ ι' = ι`, so its stalk maps at points of `U` are isos, so its sections over every open
  `W ⊆ U` are isos (Mathlib `app_isIso_of_stalkFunctor_map_iso`: a sheaf morphism which is an iso on
  stalks is an iso); restricting to `U` gives
  `(j_! G)|_U ≅ (j_* G)|_U`, and `(j_* G)|_U ≅ G` because `j⁻¹(j(V)) = V` (`Opens.map_functor_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology TopCat.Presheaf
open scoped AlgebraicGeometry

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)
  (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})

/-- The stalk of the presheaf `P = extendByZeroPresheaf U G` at a point `x ∉ U` is zero: every germ is
the germ of a section over some open `V ∋ x`, and `V ⊄ U` forces `P(V) = 0`. (Stacks 00A5(3), presheaf
level.) -/
theorem isZero_extendByZeroPresheaf_stalk_of_notMem (x : X) (hx : x ∉ U) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (extendByZeroPresheaf U G) x) := by
  have key : ∀ t : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (extendByZeroPresheaf U G) x,
      t = 0 := by
    intro t
    obtain ⟨V, m, s, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X) (extendByZeroPresheaf U G) t
    have hV : ¬ V ≤ U := fun h => hx (h m)
    have hs : s = 0 := by
      apply Subtype.ext
      have h2 := (s : extendByZeroSubgroup U G (op V)).2
      simp only [extendByZeroSubgroup, unop_op, if_neg hV, AddSubgroup.mem_bot] at h2
      exact h2
    rw [hs, map_zero]
  exact @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => (key a).trans (key b).symm⟩

/-- For `x ∈ U`, the stalk map at `x` of the inclusion `ι : P ⟶ j_* G` is an isomorphism: injective
because `ι` is injective on every open, surjective because every germ of `j_* G` at `x` is represented by
a section over some open `V ⊆ U`, where `P(V) = (j_* G)(V)`. (Stacks 00A5(3), presheaf level.) -/
theorem isIso_stalkFunctor_map_extendByZeroPresheafι (x : X) (hx : x ∈ U) :
    IsIso ((stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroPresheafι U G)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨stalkFunctor_map_injective_of_app_injective (fun V a b h => Subtype.ext h) x, fun t => ?_⟩
  obtain ⟨V, hVU, m, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (extendByZeroPushforward U G) t hx
  have hs : s ∈ extendByZeroSubgroup U G (op V) := by
    simp only [extendByZeroSubgroup, if_pos hVU, AddSubgroup.mem_top]
  exact ⟨TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (extendByZeroPresheaf U G) V x m ⟨s, hs⟩,
    (stalkFunctor_map_germ_apply V x m (extendByZeroPresheafι U G) ⟨s, hs⟩).trans rfl⟩

/-- The sheaf map `j_! G ⟶ j_* G` is the adjoint transpose of `ι : P ⟶ j_* G`:
`toSheafify P ≫ extendByZeroToPushforward = ι`. -/
theorem toSheafify_comp_extendByZeroToPushforward_hom :
    toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G) ≫
      (extendByZeroToPushforward U G).hom = extendByZeroPresheafι U G := by
  show toSheafify _ _ ≫ sheafifyMap _ (extendByZeroPresheafι U G) ≫
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G)).hom = _
  erw [sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift, toSheafify_sheafifyLift,
    Category.comp_id]

/-- For `x ∈ U`, the stalk map at `x` of `j_! G ⟶ j_* G` is an isomorphism (Stacks 007Z for the unit
`P ⟶ sheafify P`, then `isIso_stalkFunctor_map_extendByZeroPresheafι`). -/
theorem isIso_stalkFunctor_map_extendByZeroToPushforward (x : X) (hx : x ∈ U) :
    IsIso ((stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroToPushforward U G).hom) := by
  have h1 := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} (extendByZeroPresheaf U G)
  have h2 := isIso_stalkFunctor_map_extendByZeroPresheafι U G x hx
  have h : (stalkFunctor AddCommGrpCat.{u} x).map (toSheafify _ (extendByZeroPresheaf U G)) ≫
      (stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroToPushforward U G).hom =
      (stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroPresheafι U G) :=
    ((stalkFunctor AddCommGrpCat.{u} x).map_comp _ _).symm.trans
      (congrArg (stalkFunctor AddCommGrpCat.{u} x).map (toSheafify_comp_extendByZeroToPushforward_hom U G))
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ h1 h2 h

/-- On an open `W ⊆ U`, the map of sections `(j_! G)(W) ⟶ (j_* G)(W)` is an isomorphism (a morphism of
sheaves whose stalk maps over `W` are isomorphisms is an isomorphism on `W`; Mathlib
`app_isIso_of_stalkFunctor_map_iso`). -/
theorem isIso_extendByZeroToPushforward_hom_app (W : Opens X) (hW : W ≤ U) :
    IsIso ((extendByZeroToPushforward U G).hom.app (op W)) := by
  have : ∀ x : W, IsIso ((stalkFunctor AddCommGrpCat.{u} x.1).map (extendByZeroToPushforward U G).hom) :=
    fun x => isIso_stalkFunctor_map_extendByZeroToPushforward U G x.1 (hW x.2)
  exact app_isIso_of_stalkFunctor_map_iso _ W

/-- The restriction to `U` of `j_! G ⟶ j_* G` is an isomorphism of sheaves on `U`: its components are
the section maps over the opens `j(V) ⊆ U`. -/
theorem isIso_restrict_map_extendByZeroToPushforward :
    IsIso (((Opens.isOpenEmbedding U).sheafPullback AddCommGrpCat.{u}).map (extendByZeroToPushforward U G)) := by
  have h1 : ∀ V, IsIso (((sheafToPresheaf _ _).map
      (((Opens.isOpenEmbedding U).sheafPullback AddCommGrpCat.{u}).map (extendByZeroToPushforward U G))).app V) := by
    intro V
    show IsIso ((extendByZeroToPushforward U G).hom.app (op ((Opens.isOpenEmbedding U).functor.obj V.unop)))
    exact isIso_extendByZeroToPushforward_hom_app U G _ (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have h2 : IsIso ((sheafToPresheaf _ _).map (((Opens.isOpenEmbedding U).sheafPullback AddCommGrpCat.{u}).map
      (extendByZeroToPushforward U G))) := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h1
  exact @isIso_of_fully_faithful _ _ _ _ (sheafToPresheaf _ _) _ _ _ _ _ h2

/-- Presheaf level: `j⁻¹ j_* G ≅ G` for the naive restriction along the open embedding `j : U ↪ X`,
componentwise `G(j⁻¹(j(V))) = G(V)` (`Opens.map_functor_eq`). -/
def restrictPushforwardPresheafIso :
    (Opens.isOpenEmbedding U).functor.op ⋙ (Opens.map (Opens.inclusion' U)).op ⋙ G.obj ≅ G.obj :=
  NatIso.ofComponents (fun V => G.obj.mapIso (eqToIso (congrArg op (Opens.map_functor_eq V.unop))))
    (fun {V W} f => by
      show G.obj.map _ ≫ G.obj.map _ = G.obj.map _ ≫ G.obj.map _
      exact ((G.obj.map_comp _ _).symm.trans (congrArg G.obj.map (Subsingleton.elim _ _))).trans
        (G.obj.map_comp _ _))

/-- `(j_* G)|_U ≅ G` for the naive restriction `TopCat.Sheaf.restrict` along the open embedding
`j : U ↪ X`. -/
def restrictPushforwardIso :
    TopCat.Sheaf.restrict ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G) U ≅ G :=
  (sheafToPresheaf _ _).preimageIso (restrictPushforwardPresheafIso U G)

end TopCat.Sheaf

/-- Stacks 00A5 (3)(5): for `j : U ↪ X` open and `G` an abelian sheaf on `U`,
`j_!G = TopCat.Sheaf.extendByZero U G` satisfies `(j_!G)_x ≅ G_x` for `x ∈ U`, `(j_!G)_x = 0` for `x ∉ U`,
and `j^{-1}j_!G ≅ G`. -/

theorem TopCat.Sheaf.extendByZero_stalk_of_mem {X : TopCat.{u}} (U : TopologicalSpace.Opens X)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})
    (x : X) (hx : x ∈ U) :
    Nonempty (TopCat.Presheaf.stalk (TopCat.Sheaf.extendByZero U G).obj x ≅
      TopCat.Presheaf.stalk (show TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of U) from G.obj) (⟨x, hx⟩ : U)) := by
  have h1 := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} (extendByZeroPresheaf U G)
  have h2 := isIso_stalkFunctor_map_extendByZeroPresheafι U G x hx
  have h3 := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
    (Opens.isOpenEmbedding U).isInducing (G.obj : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of U)) ⟨x, hx⟩
  exact ⟨(@asIso _ _ _ _ _ h1).symm ≪≫ @asIso _ _ _ _ _ h2 ≪≫ @asIso _ _ _ _ _ h3⟩

theorem TopCat.Sheaf.isZero_extendByZero_stalk_of_notMem {X : TopCat.{u}} (U : TopologicalSpace.Opens X)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})
    (x : X) (hx : x ∉ U) :
    CategoryTheory.Limits.IsZero (TopCat.Presheaf.stalk (TopCat.Sheaf.extendByZero U G).obj x) := by
  have h1 := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} (extendByZeroPresheaf U G)
  exact (isZero_extendByZeroPresheaf_stalk_of_notMem U G x hx).of_iso (@asIso _ _ _ _ _ h1).symm

theorem TopCat.Sheaf.restrict_extendByZero_iso {X : TopCat.{u}} (U : TopologicalSpace.Opens X)
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    Nonempty (TopCat.Sheaf.restrict (TopCat.Sheaf.extendByZero U G) U ≅ G) := by
  have h1 := isIso_restrict_map_extendByZeroToPushforward U G
  exact ⟨@asIso _ _ _ _ _ h1 ≪≫ restrictPushforwardIso U G⟩

end
