import MiyaokaMori.Prelude

/-! # Stalk lemmas for Stacks 02UT (generic, for presheaves of abelian groups)

Three small facts about stalks of `AddCommGrpCat`-valued presheaves on a topological space,
used to check the sequence `0 → j_!j^*F → F → i_*i^*F → 0` of Stacks 02UT on stalks:

* `stalkFunctor_map_bijective_of_app_bijective_of_le`: a morphism of presheaves that is bijective
  on every open `V ≤ U` induces a bijection on stalks at every `x ∈ U` (germs at `x` can be
  represented on opens inside `U`; Stacks 007Z / 00A5-style argument);
* `isZero_stalk_of_subsingleton_of_le`: if the sections over every open neighbourhood `V ≤ W` of `x`
  are trivial, the stalk at `x ∈ W` is zero;
* `stalkFunctor_map_pushforward_stalkPushforward`: naturality of Mathlib's
  `TopCat.Presheaf.stalkPushforward` in the presheaf (`(f_* α)_{f x}` followed by the comparison
  map equals the comparison map followed by `α_x`).

Source: Stacks 02UT (proof, "check on stalks"); Stacks 00A5. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- If `φ.app (op V)` is bijective for every open `V ≤ U`, then the stalk map of `φ` is bijective
at every point of `U`. -/
theorem stalkFunctor_map_bijective_of_app_bijective_of_le
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (φ : P ⟶ Q) (U : Opens X) (x : X) (hx : x ∈ U)
    (h : ∀ V : Opens X, V ≤ U → Function.Bijective (φ.app (op V))) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ) := by
  constructor
  · -- injectivity: it suffices to show the kernel is trivial
    refine (injective_iff_map_eq_zero _).mpr ?_
    intro t ht
    obtain ⟨V, hxV, s, rfl⟩ := P.exists_germ_eq t
    have hxV' : x ∈ V ⊓ U := ⟨hxV, hx⟩
    set s' : P.obj (op (V ⊓ U)) := P.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s with hs'
    have hgerm : P.germ V x hxV s = P.germ (V ⊓ U) x hxV' s' := by
      rw [hs', P.germ_res_apply]
    rw [hgerm] at ht ⊢
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ht
    have ht' : Q.germ (V ⊓ U) x hxV' (φ.app (op (V ⊓ U)) s') =
        Q.germ (V ⊓ U) x hxV' 0 := by
      rw [ht, map_zero]
      rfl
    obtain ⟨W, hxW, iW₁, iW₂, heq⟩ := Q.germ_eq x hxV' hxV' _ _ ht'
    rw [map_zero] at heq
    have hnat : φ.app (op W) (P.map iW₁.op s') = Q.map iW₁.op (φ.app (op (V ⊓ U)) s') := by
      have := congrArg (fun g => g (s')) (φ.naturality iW₁.op)
      simp only [ConcreteCategory.comp_apply] at this
      exact this
    have hW : W ≤ U := le_trans (leOfHom iW₁) inf_le_right
    have hzero : P.map iW₁.op s' = 0 := by
      apply (h W hW).1
      rw [hnat, heq, map_zero]
    rw [← P.germ_res_apply iW₁ x hxW s', hzero, map_zero]
    rfl
  · -- surjectivity
    intro t
    obtain ⟨V, hxV, s, rfl⟩ := Q.exists_germ_eq t
    have hxV' : x ∈ V ⊓ U := ⟨hxV, hx⟩
    obtain ⟨p, hp⟩ := (h (V ⊓ U) inf_le_right).2 (Q.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s)
    refine ⟨P.germ (V ⊓ U) x hxV' p, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hp, Q.germ_res_apply]

/-- If the sections of `P` over every open neighbourhood `V ≤ W` of `x` are trivial, the stalk of `P`
at `x ∈ W` is zero. -/
theorem isZero_stalk_of_subsingleton_of_le (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    (W : Opens X) (x : X) (hx : x ∈ W)
    (h : ∀ V : Opens X, x ∈ V → V ≤ W → Subsingleton (P.obj (op V))) :
    IsZero (P.stalk x) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  constructor
  intro a b
  suffices hzero : ∀ t : P.stalk x, t = 0 by
    rw [hzero a, hzero b]
  intro t
  obtain ⟨V, hxV, s, rfl⟩ := P.exists_germ_eq t
  have hxV' : x ∈ V ⊓ W := ⟨hxV, hx⟩
  have hres : P.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op s = 0 :=
    (h (V ⊓ W) hxV' inf_le_right).elim _ _
  rw [← P.germ_res_apply (homOfLE (inf_le_left : V ⊓ W ≤ V)) x hxV' s, hres, map_zero]

/-- Naturality of `stalkPushforward` in the presheaf. -/
theorem stalkFunctor_map_pushforward_stalkPushforward {Y : TopCat.{u}} (f : X ⟶ Y)
    {G G' : TopCat.Presheaf AddCommGrpCat.{u} X} (α : G ⟶ G') (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α) ≫
      G'.stalkPushforward AddCommGrpCat.{u} f x =
    G.stalkPushforward AddCommGrpCat.{u} f x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hxV
  have h1 : ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj G).germ V (f x) hxV ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α) =
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α).app (op V) ≫
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj G').germ V (f x) hxV :=
    TopCat.Presheaf.stalkFunctor_map_germ V (f x) hxV _
  have h2 : G.germ ((Opens.map f).obj V) x hxV ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α =
      α.app (op ((Opens.map f).obj V)) ≫ G'.germ ((Opens.map f).obj V) x hxV :=
    TopCat.Presheaf.stalkFunctor_map_germ _ x hxV α
  erw [← Category.assoc, h1, Category.assoc, TopCat.Presheaf.stalkPushforward_germ,
    ← Category.assoc, TopCat.Presheaf.stalkPushforward_germ, h2]
  rfl

end TopCat.Presheaf

end
