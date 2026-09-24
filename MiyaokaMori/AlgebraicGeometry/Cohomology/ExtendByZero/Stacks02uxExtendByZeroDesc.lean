import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uzExtendByZero

/-! # Morphisms out of an extension by zero: `extendByZeroDesc` (the transpose along `j_! ⊣ j^{-1}`)

For an open `j : U ↪ X`, an abelian sheaf `G` on `U`, an abelian sheaf `F` on `X` and a morphism
`α : G ⟶ F|_U` (naive restriction `TopCat.Sheaf.restrict F U`, `(F|_U)(W) = F(j(W))`), we build
`extendByZeroDesc U α : j_!G ⟶ F`:
* on the presheaf `P = extendByZeroPresheaf U G` (`P(V) = G(j⁻¹V)` if `V ⊆ U`, else `0`) it is
  `α_{j⁻¹V}` followed by `F(j(j⁻¹V)) = F(V ⊓ U) ⟶ F(V)` when `V ⊆ U`, and `0` otherwise
  (`extendByZeroDescPresheaf`);
* then `sheafifyLift`, since `j_!G` is the sheafification of `P` (`extendByZero_eq_sheafify` is `rfl`).

Properties proved here:
* `toSheafify_extendByZeroDesc_val`: `toSheafify P ≫ (extendByZeroDesc U α).hom = extendByZeroDescPresheaf U α`
  (the value on sections coming from `P`);
* `extendByZeroDesc_comp_restrictUnit`: composing with the restriction map `F ⟶ j_*(F|_U)` (`restrictUnit`)
  gives `extendByZeroToPushforward U G ≫ j_*α`;
* `extendByZeroDesc_mono_of_isIso`: if `α` is an isomorphism then `extendByZeroDesc U α` is a monomorphism
  (because `j_!G ⟶ j_*G` is one).

Source: Stacks 00A5 (sheaves-lemma-j-shriek-abelian), the adjunction `j_! ⊣ j^{-1}`; used for Stacks 02UX. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)

theorem le_functor_map_of_le (V : Opens X) (hV : V ≤ U) :
    V ≤ (Opens.isOpenEmbedding U).functor.obj ((Opens.map (Opens.inclusion' U)).obj V) := by
  rw [Opens.functor_map_eq_inf]
  exact le_inf le_rfl hV

theorem functor_map_le (V : Opens X) :
    (Opens.isOpenEmbedding U).functor.obj ((Opens.map (Opens.inclusion' U)).obj V) ≤ V := by
  rw [Opens.functor_map_eq_inf]
  exact inf_le_left

/-- folding two applications of a functor to `AddCommGrpCat` into one -/
theorem map_comp_hom_apply {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u}) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (x : F.obj A) :
    (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by
  rw [F.map_comp]
  rfl

variable {G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}}
  {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- the component at `V` of the presheaf map `P ⟶ F.val`: `α_{j⁻¹V}` then restriction, or `0` -/
def extendByZeroDescApp (α : G ⟶ TopCat.Sheaf.restrict F U) (V : (Opens X)ᵒᵖ) :
    (extendByZeroPresheaf U G).obj V ⟶ F.obj.obj V :=
  open Classical in
  if hV : V.unop ≤ U then
    AddCommGrpCat.ofHom
      (((F.obj.map (homOfLE (le_functor_map_of_le U V.unop hV)).op).hom.comp
        (α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj V.unop))).hom).comp
          (extendByZeroSubgroup U G V).subtype)
  else 0

theorem extendByZeroDescApp_of_le (α : G ⟶ TopCat.Sheaf.restrict F U) (V : (Opens X)ᵒᵖ)
    (hV : V.unop ≤ U) (x : (extendByZeroPresheaf U G).obj V) :
    (extendByZeroDescApp U α V).hom x =
      (F.obj.map (homOfLE (le_functor_map_of_le U V.unop hV)).op).hom
        ((α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj V.unop))).hom
          ((extendByZeroSubgroup U G V).subtype x)) := by
  have h : extendByZeroDescApp U α V = AddCommGrpCat.ofHom
      (((F.obj.map (homOfLE (le_functor_map_of_le U V.unop hV)).op).hom.comp
        (α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj V.unop))).hom).comp
          (extendByZeroSubgroup U G V).subtype) := by
    unfold extendByZeroDescApp
    exact dif_pos hV
  rw [h]
  rfl

theorem extendByZeroDescApp_of_not_le (α : G ⟶ TopCat.Sheaf.restrict F U) (V : (Opens X)ᵒᵖ)
    (hV : ¬ V.unop ≤ U) (x : (extendByZeroPresheaf U G).obj V) :
    (extendByZeroDescApp U α V).hom x = 0 := by
  have h : extendByZeroDescApp U α V = 0 := by
    unfold extendByZeroDescApp
    exact dif_neg hV
  rw [h]
  rfl

theorem extendByZeroPresheaf_eq_zero_of_not_le (V : (Opens X)ᵒᵖ) (hV : ¬ V.unop ≤ U)
    (x : (extendByZeroPresheaf U G).obj V) : x = 0 := by
  have hx := x.2
  simp only [extendByZeroSubgroup, if_neg hV, AddSubgroup.mem_bot] at hx
  exact Subtype.ext hx

/-- the presheaf map `P ⟶ F.val` -/
def extendByZeroDescPresheaf (α : G ⟶ TopCat.Sheaf.restrict F U) :
    extendByZeroPresheaf U G ⟶ F.obj where
  app V := extendByZeroDescApp U α V
  naturality := by
    intro V W f
    ext x
    change (extendByZeroDescApp U α W).hom (((extendByZeroPresheaf U G).map f).hom x) =
      (F.obj.map f).hom ((extendByZeroDescApp U α V).hom x)
    by_cases hW : W.unop ≤ U
    · by_cases hV : V.unop ≤ U
      · rw [extendByZeroDescApp_of_le U α W hW, extendByZeroDescApp_of_le U α V hV]
        -- `(P.map f x).val = (j_*G).map f x.val`
        change (F.obj.map (homOfLE (le_functor_map_of_le U W.unop hW)).op).hom
            ((α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj W.unop))).hom
              ((G.obj.map ((Opens.map (Opens.inclusion' U)).op.map f)).hom
                ((extendByZeroSubgroup U G V).subtype x))) = _
        have hnat : (α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj W.unop))).hom
              ((G.obj.map ((Opens.map (Opens.inclusion' U)).op.map f)).hom
                ((extendByZeroSubgroup U G V).subtype x)) =
            ((TopCat.Sheaf.restrict F U).obj.map ((Opens.map (Opens.inclusion' U)).op.map f)).hom
              ((α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj V.unop))).hom
                ((extendByZeroSubgroup U G V).subtype x)) :=
          congrArg (fun g => g.hom ((extendByZeroSubgroup U G V).subtype x))
            (α.hom.naturality ((Opens.map (Opens.inclusion' U)).op.map f))
        refine Eq.trans (congrArg (F.obj.map (homOfLE (le_functor_map_of_le U W.unop hW)).op).hom hnat) ?_
        have heq : (Opens.isOpenEmbedding U).functor.op.map ((Opens.map (Opens.inclusion' U)).op.map f) ≫
            (homOfLE (le_functor_map_of_le U W.unop hW)).op =
            (homOfLE (le_functor_map_of_le U V.unop hV)).op ≫ f :=
          Quiver.Hom.unop_inj (Subsingleton.elim _ _)
        refine Eq.trans (map_comp_hom_apply F.obj
          ((Opens.isOpenEmbedding U).functor.op.map ((Opens.map (Opens.inclusion' U)).op.map f))
          (homOfLE (le_functor_map_of_le U W.unop hW)).op _) ?_
        refine Eq.trans (congrArg (fun m => (F.obj.map m).hom _) heq) ?_
        exact (map_comp_hom_apply F.obj _ _ _).symm
      · have hx : x = 0 := extendByZeroPresheaf_eq_zero_of_not_le U V hV x
        rw [hx, map_zero, map_zero, extendByZeroDescApp_of_not_le U α V hV, map_zero]
    · have hV : ¬ V.unop ≤ U := fun h => hW (le_trans (leOfHom f.unop) h)
      rw [extendByZeroDescApp_of_not_le U α W hW, extendByZeroDescApp_of_not_le U α V hV, map_zero]

/-- **`extendByZeroDesc`**: the morphism `j_!G ⟶ F` induced by `α : G ⟶ F|_U`. -/
def extendByZeroDesc (α : G ⟶ TopCat.Sheaf.restrict F U) : TopCat.Sheaf.extendByZero U G ⟶ F :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (extendByZeroDescPresheaf U α) F.property⟩

theorem toSheafify_extendByZeroDesc_val (α : G ⟶ TopCat.Sheaf.restrict F U) :
    toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G) ≫ (extendByZeroDesc U α).hom =
      extendByZeroDescPresheaf U α :=
  toSheafify_sheafifyLift _ _ _

/-- value of `extendByZeroDesc U α` on a section coming from the presheaf `P` -/
theorem extendByZeroDesc_val_app_toSheafify (α : G ⟶ TopCat.Sheaf.restrict F U) (V : (Opens X)ᵒᵖ)
    (x : (extendByZeroPresheaf U G).obj V) :
    ((extendByZeroDesc U α).hom.app V).hom
        (((toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G)).app V).hom x) =
      (extendByZeroDescApp U α V).hom x := by
  exact congrArg (fun g => (g.app V).hom x) (toSheafify_extendByZeroDesc_val U α)

/-- the restriction map `F ⟶ j_*(F|_U)` (on `V`: `F(V) ⟶ F(V ⊓ U)`) -/
def restrictUnit (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj (TopCat.Sheaf.restrict F U) where
  hom :=
    { app := fun V => F.obj.map (homOfLE (functor_map_le U V.unop)).op
      naturality := by
        intro V W f
        change F.obj.map f ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        congr 1 }

/-- `toSheafify P ≫ (j_!G ⟶ j_*G) = (P ⟶ j_*G)`: the mono `extendByZeroToPushforward` on sections from `P` -/
theorem toSheafify_extendByZeroToPushforward_hom :
    toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G) ≫
      (extendByZeroToPushforward U G).hom = extendByZeroPresheafι U G := by
  have h : (extendByZeroToPushforward U G).hom =
      sheafifyMap (Opens.grothendieckTopology X) (extendByZeroPresheafι U G) ≫
        ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G)).hom := rfl
  erw [h, sheafificationAdjunction_counit_app_val, ← toSheafify_naturality_assoc, toSheafify_sheafifyLift,
    Category.comp_id]

theorem extendByZeroDesc_comp_restrictUnit (α : G ⟶ TopCat.Sheaf.restrict F U) :
    extendByZeroDesc U α ≫ restrictUnit U F =
      extendByZeroToPushforward U G ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α := by
  apply CategoryTheory.Sheaf.hom_ext
  refine sheafify_hom_ext (Opens.grothendieckTopology X) (P := extendByZeroPresheaf U G) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj
      (TopCat.Sheaf.restrict F U)).property ?_
  have h1 : toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G) ≫
      (extendByZeroDesc U α ≫ restrictUnit U F).hom =
      extendByZeroDescPresheaf U α ≫ (restrictUnit U F).hom := by
    have e : (extendByZeroDesc U α ≫ restrictUnit U F).hom =
        (extendByZeroDesc U α).hom ≫ (restrictUnit U F).hom := rfl
    erw [e, ← Category.assoc, toSheafify_extendByZeroDesc_val]
  have h2 : toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G) ≫
      (extendByZeroToPushforward U G ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α).hom =
      extendByZeroPresheafι U G ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α).hom := by
    have e : (extendByZeroToPushforward U G ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α).hom =
        (extendByZeroToPushforward U G).hom ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α).hom := rfl
    erw [e, ← Category.assoc, toSheafify_extendByZeroToPushforward_hom]
  erw [h1, h2]
  ext V x
  change ((restrictUnit U F).hom.app V).hom ((extendByZeroDescApp U α V).hom x) =
    (α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj V.unop))).hom
      ((extendByZeroSubgroup U G V).subtype x)
  by_cases hV : V.unop ≤ U
  · rw [extendByZeroDescApp_of_le U α V hV]
    refine Eq.trans (map_comp_hom_apply F.obj _ _ _) ?_
    have hid : (homOfLE (le_functor_map_of_le U V.unop hV)).op ≫ (homOfLE (functor_map_le U V.unop)).op =
        𝟙 _ :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    refine Eq.trans (congrArg (fun m => (F.obj.map m).hom _) hid) ?_
    have hid2 := F.obj.map_id (op ((Opens.isOpenEmbedding U).functor.obj
      ((Opens.map (Opens.inclusion' U)).obj V.unop)))
    exact congrArg (fun m => m.hom ((α.hom.app (op ((Opens.map (Opens.inclusion' U)).obj V.unop))).hom
      ((extendByZeroSubgroup U G V).subtype x))) hid2
  · have hx : x = 0 := extendByZeroPresheaf_eq_zero_of_not_le U V hV x
    subst hx
    rw [extendByZeroDescApp_of_not_le U α V hV]
    exact (map_zero _).trans ((congrArg (α.hom.app _).hom (map_zero _)).trans (map_zero _)).symm

/-- `extendByZeroDesc U α` is a monomorphism when `α` is an isomorphism (stated as a theorem, not an
instance). -/
theorem extendByZeroDesc_mono_of_isIso (α : G ⟶ TopCat.Sheaf.restrict F U) [IsIso α] :
    Mono (extendByZeroDesc U α) := by
  have h := extendByZeroDesc_comp_restrictUnit U α
  have hm : Mono (extendByZeroToPushforward U G ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α) := by
    have hm1 := extendByZeroToPushforward_mono U G
    have hi : IsIso ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α) :=
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).mapIso
        (asIso α : G ≅ TopCat.Sheaf.restrict F U)).isIso_hom
    have hm2 : Mono ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map α) :=
      IsIso.mono_of_iso _
    exact @mono_comp _ _ _ _ _ _ hm1 _ hm2
  exact mono_of_mono_fac h

end TopCat.Sheaf

end
