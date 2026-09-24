import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uzExtendByZero
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02utStalkAux

/-! # The counit `j_!j^*F ⟶ F` and the stalks of `j_!`

Let `j : U → X` be the inclusion of an open subset and `F` an abelian sheaf on `X`. Following
`Stacks02uzExtendByZero.lean`, `j_!j^*F = extendByZero U (restrict F U)` is the sheafification of the
subpresheaf `P ⊆ j_*j^*F` with `P(V) = (j^*F)(j⁻¹V) = F(j(j⁻¹V))` for `V ⊆ U` and `P(V) = 0` otherwise.

* `extendByZeroCounitPresheaf : P ⟶ F`: for `V ⊆ U` the identification `P(V) = F(j(j⁻¹V)) = F(V)`
  (`j(j⁻¹V) = V ⊓ U = V`, Mathlib `Opens.functor_map_eq_inf`), and `0` for `V ⊄ U`;
* `extendByZeroCounit : j_!j^*F ⟶ F`: the induced map on the sheafification (the counit of `j_! ⊣ j^*`);
* stalks: at `x ∈ U` the counit is an isomorphism on stalks
  (`isIso_stalkFunctor_map_extendByZeroCounit_hom_of_mem`: sheafification does not change stalks and
  `P ⟶ F` is bijective on every open `V ≤ U`), at `x ∉ U` the stalk of `j_!G` is zero
  (`isZero_stalk_extendByZero_of_notMem`: every open neighbourhood of `x` is not inside `U`, so `P` has
  no sections there); and `extendByZero_stalk_iso_of_mem`: `(j_!G)_x ≅ G_x` for `x ∈ U` (Stacks 00A5 (3)).

Source: Stacks 02UT (the map `j_!j^*F → F` and its stalks), Stacks 00A5 (3). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)

/-- For `V ≤ U`, `j(j⁻¹V) = V`. -/
theorem functor_map_obj_eq_of_le (V : Opens X) (hV : V ≤ U) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V := by
  rw [Opens.functor_map_eq_inf]
  exact inf_eq_left.mpr hV

/-- Sections of the subpresheaf `P ⊆ j_* G` over an open `V ⊄ U` vanish. -/
theorem extendByZeroSubgroup_val_eq_zero_of_not_le
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) {V : (Opens X)ᵒᵖ}
    (hV : ¬ V.unop ≤ U) (s : extendByZeroSubgroup U G V) :
    (s : (extendByZeroPushforward U G).obj V) = 0 := by
  have hs := s.2
  simp only [extendByZeroSubgroup, if_neg hV, AddSubgroup.mem_bot] at hs
  exact hs

/-- Over an open `V ≤ U`, the subpresheaf `P ⊆ j_* G` is everything. -/
theorem extendByZeroSubgroup_eq_top_of_le
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) {V : (Opens X)ᵒᵖ}
    (hV : V.unop ≤ U) : extendByZeroSubgroup U G V = ⊤ := by
  simp only [extendByZeroSubgroup, if_pos hV]

variable (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Over an open `V ⊄ U` the presheaf `P` (`extendByZeroPresheaf`) is zero. -/
theorem isZero_extendByZeroPresheaf_obj_of_not_le
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) {V : (Opens X)ᵒᵖ}
    (hV : ¬ V.unop ≤ U) : IsZero ((extendByZeroPresheaf U G).obj V) := by
  have : Subsingleton ((extendByZeroPresheaf U G).obj V) := ⟨fun a b => Subtype.ext (by
    rw [extendByZeroSubgroup_val_eq_zero_of_not_le U G hV a,
      extendByZeroSubgroup_val_eq_zero_of_not_le U G hV b])⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The identification `op (j(j⁻¹V)) = V` for `V ≤ U`, as a morphism of `(Opens X)ᵒᵖ`. -/
abbrev extendByZeroCounitEqToHom {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V.unop)) ⟶ V :=
  eqToHom (congrArg op (functor_map_obj_eq_of_le U V.unop hV))

/-- For `V ≤ U`: the identification `(j_*j^*F)(V) = F(j(j⁻¹V)) = F(V)`, stated with source
`(extendByZeroPushforward U (restrict F U)).obj V` (definitionally `F(j(j⁻¹V))`). -/
def extendByZeroCounitRes {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    (extendByZeroPushforward U (TopCat.Sheaf.restrict F U)).obj V ⟶ F.obj.obj V :=
  F.obj.map (extendByZeroCounitEqToHom U hV)

theorem extendByZeroCounitRes_eq {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    extendByZeroCounitRes U F hV = F.obj.map (extendByZeroCounitEqToHom U hV) := rfl

open Classical in
/-- The component at `V` of the counit `P ⟶ F` on the presheaf `P` (`extendByZeroPresheaf`) whose
sheafification is `j_!j^*F`: for `V ≤ U` it is the inclusion `P(V) ⊆ (j_*j^*F)(V) = F(j(j⁻¹V))`
followed by the identification `j(j⁻¹V) = V`; for `V ⊄ U` it is `0` (there `P(V) = 0`). -/
def extendByZeroCounitPresheafApp (V : (Opens X)ᵒᵖ) :
    (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U)).obj V ⟶ F.obj.obj V :=
  if hV : V.unop ≤ U then
    (extendByZeroPresheafι U (TopCat.Sheaf.restrict F U)).app V ≫ extendByZeroCounitRes U F hV
  else 0

theorem extendByZeroCounitPresheafApp_of_le {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    extendByZeroCounitPresheafApp U F V =
      (extendByZeroPresheafι U (TopCat.Sheaf.restrict F U)).app V ≫ extendByZeroCounitRes U F hV := by
  unfold extendByZeroCounitPresheafApp
  exact dif_pos hV

theorem extendByZeroCounitPresheafApp_of_not_le {V : (Opens X)ᵒᵖ} (hV : ¬ V.unop ≤ U) :
    extendByZeroCounitPresheafApp U F V = 0 := by
  unfold extendByZeroCounitPresheafApp
  exact dif_neg hV

/-- The counit `P ⟶ F` at the presheaf level. -/
def extendByZeroCounitPresheaf : extendByZeroPresheaf U (TopCat.Sheaf.restrict F U) ⟶ F.obj where
  app := extendByZeroCounitPresheafApp U F
  naturality := by
    intro V W f
    by_cases hW : W.unop ≤ U
    · by_cases hV : V.unop ≤ U
      · rw [extendByZeroCounitPresheafApp_of_le U F hV, extendByZeroCounitPresheafApp_of_le U F hW,
          ← Category.assoc, (extendByZeroPresheafι U (TopCat.Sheaf.restrict F U)).naturality f,
          Category.assoc, Category.assoc]
        congr 1
        rw [extendByZeroCounitRes_eq, extendByZeroCounitRes_eq]
        change F.obj.map (U.isOpenEmbedding.functor.op.map ((Opens.map U.inclusion').op.map f)) ≫
            F.obj.map (extendByZeroCounitEqToHom U hW) =
          F.obj.map (extendByZeroCounitEqToHom U hV) ≫ F.obj.map f
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        exact congrArg F.obj.map (Subsingleton.elim _ _)
      · rw [extendByZeroCounitPresheafApp_of_not_le U F hV, zero_comp]
        exact (isZero_extendByZeroPresheaf_obj_of_not_le U _ hV).eq_zero_of_src _
    · have hV : ¬ V.unop ≤ U := fun h => hW (le_trans (leOfHom f.unop) h)
      rw [extendByZeroCounitPresheafApp_of_not_le U F hW, comp_zero]
      exact ((isZero_extendByZeroPresheaf_obj_of_not_le U _ hV).eq_zero_of_src _).symm

/-- The counit `j_!j^*F ⟶ F` (Stacks 02UT, the first map of the sequence), obtained from the
presheaf-level counit by the sheafification adjunction. -/
def extendByZeroCounit :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U)) ⟶ F :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv
    (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U)) F).symm (extendByZeroCounitPresheaf U F)

theorem toSheafify_comp_extendByZeroCounit_hom :
    toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U)) ≫
      (extendByZeroCounit U F).hom = extendByZeroCounitPresheaf U F := by
  have h := ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv
    (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U)) F).apply_symm_apply
    (extendByZeroCounitPresheaf U F)
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- Over `V ≤ U` the presheaf counit is bijective. -/
theorem bijective_extendByZeroCounitPresheaf_app_of_le (V : Opens X) (hV : V ≤ U) :
    Function.Bijective ((extendByZeroCounitPresheaf U F).app (op V)) := by
  have hV' : (op V).unop ≤ U := hV
  change Function.Bijective (extendByZeroCounitPresheafApp U F (op V))
  rw [extendByZeroCounitPresheafApp_of_le U F hV', ConcreteCategory.coe_comp]
  have hres : IsIso (extendByZeroCounitRes U F hV') := by
    rw [extendByZeroCounitRes_eq]
    exact (F.obj.mapIso (eqToIso (congrArg op (functor_map_obj_eq_of_le U (op V).unop hV')))).isIso_hom
  refine Function.Bijective.comp
    (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ (extendByZeroCounitRes U F hV') hres) ⟨?_, ?_⟩
  · intro a b hab
    exact Subtype.ext hab
  · intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [extendByZeroSubgroup_eq_top_of_le U _ hV']
    exact AddSubgroup.mem_top y

/-- At `x ∈ U`, the counit `j_!j^*F ⟶ F` is an isomorphism on stalks. -/
theorem isIso_stalkFunctor_map_extendByZeroCounit_hom_of_mem (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroCounit U F).hom) := by
  haveI h1 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U)))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroCounitPresheaf U F)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (TopCat.Presheaf.stalkFunctor_map_bijective_of_app_bijective_of_le _ U x hx
        (fun V hV => bijective_extendByZeroCounitPresheaf_app_of_le U F V hV))
  have h3 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U))) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroCounit U F).hom =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroCounitPresheaf U F) := by
    rw [← Functor.map_comp, toSheafify_comp_extendByZeroCounit_hom]
  rw [← h3] at h2
  haveI := h2
  exact IsIso.of_isIso_comp_left ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U (TopCat.Sheaf.restrict F U))))
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroCounit U F).hom)

/-- The stalk of the presheaf `P` at `x ∉ U` is zero. -/
theorem isZero_stalk_extendByZeroPresheaf_of_notMem
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) (x : X) (hx : x ∉ U) :
    IsZero (TopCat.Presheaf.stalk (extendByZeroPresheaf U G) x) := by
  apply TopCat.Presheaf.isZero_stalk_of_subsingleton_of_le _ ⊤ x _root_.trivial
  intro V hxV _
  have hV : ¬ (op V).unop ≤ U := fun h => hx (h hxV)
  constructor
  intro a b
  apply Subtype.ext
  rw [extendByZeroSubgroup_val_eq_zero_of_not_le U G hV a,
    extendByZeroSubgroup_val_eq_zero_of_not_le U G hV b]

/-- The stalk of `j_!G` at `x ∉ U` is zero (Stacks 00A5 (3)). -/
theorem isZero_stalk_extendByZero_of_notMem
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) (x : X) (hx : x ∉ U) :
    IsZero (TopCat.Presheaf.stalk (TopCat.Sheaf.extendByZero U G).obj x) := by
  haveI h1 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  exact (isZero_stalk_extendByZeroPresheaf_of_notMem U G x hx).of_iso
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G)))).symm

/-- Stacks 00A5 (3), at `x ∈ U`: the stalk of `j_!G` is the stalk of `G` at `x`. Proof: sheafification
does not change stalks (`stalkFunctor_map_unit_toSheafify_isIso`); the inclusion `P ⟶ j_*G` is bijective
over every open `V ≤ U` (there `P(V) = (j_*G)(V)`), hence on stalks at `x ∈ U`
(`stalkFunctor_map_bijective_of_app_bijective_of_le`); and `(j_*G)_{j x} ≅ G_x` since `j` is inducing
(Mathlib `stalkPushforward_iso_of_isInducing`). Compare `extendByZero_stalk_of_mem` in
`ExtendByZeroStalk.lean`. -/
theorem extendByZero_stalk_iso_of_mem
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) (x : X) (hx : x ∈ U) :
    Nonempty (TopCat.Presheaf.stalk (TopCat.Sheaf.extendByZero U G).obj x ≅
      TopCat.Presheaf.stalk (show TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of U) from G.obj)
        (⟨x, hx⟩ : U)) := by
  have h1 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (extendByZeroPresheaf U G))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have h2 : Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (extendByZeroPresheafι U G)) := by
    refine TopCat.Presheaf.stalkFunctor_map_bijective_of_app_bijective_of_le _ U x hx (fun V hV => ?_)
    have hV' : (op V).unop ≤ U := hV
    refine ⟨fun a b hab => Subtype.ext hab, fun y => ⟨⟨y, ?_⟩, rfl⟩⟩
    rw [extendByZeroSubgroup_eq_top_of_le U G hV']
    exact AddSubgroup.mem_top y
  have h2' : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroPresheafι U G)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h2
  have h3 : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (Opens.inclusion' U) G.obj
      (⟨x, hx⟩ : U)) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
      (Opens.isOpenEmbedding U).isInducing G.obj ⟨x, hx⟩
  exact ⟨(@asIso _ _ _ _ _ h1).symm ≪≫ @asIso _ _ _ _ _ h2' ≪≫ @asIso _ _ _ _ _ h3⟩

end TopCat.Sheaf

end
