import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.TopcatSheafOpenClosedFunctors

/-! # Extension by zero: support and functoriality

Complements to `TopCat.Sheaf.extendByZero` (`j_!`, defined in `TopcatSheafOpenClosedFunctors.lean`
as the sheafification of the subpresheaf `V ↦ G(V)` if `V ⊆ U`, else `0`, of `j_* G`):
* `extendByZeroPresheaf`: that subpresheaf, with `extendByZero U G = sheafify(extendByZeroPresheaf U G)`
  by `rfl`;
* `extendByZeroToPushforward`: the monomorphism `j_! G ⟶ j_* G` (sheafification is left exact);
* **support** (the second half of Stacks 02UT, missing from `shortExact_extendByZero_restrict`):
  `j_! G` restricted to an open `V` disjoint from `U` is zero
  (`isZero_restrict_extendByZero_of_disjoint`), because its sections inject into
  `(j_* G)(V') = G(V' ∩ U) = G(∅) = 0`;
* `extendByZeroFunctor`: `j_!` as a functor (needed to transport isomorphisms), and `j_!(0) = 0`;
* `restrictConstantSheafIso`: `(ℤ_X)|_U ≅ ℤ_U` (both are left adjoint to global sections, as in
  `constantSheafPullbackAbIso` of `Stacks02uv.lean`).

Source: Stacks 02UT (cohomology-lemma-extension-by-zero, "j_!j^*F is supported on the closure of U"). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)

/-- the pushforward `j_* G` as a presheaf on `X` -/
abbrev extendByZeroPushforward
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G).obj

open Classical in
/-- the subgroup `G(V)` if `V ⊆ U`, else `0` -/
def extendByZeroSubgroup
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) (V : (Opens X)ᵒᵖ) :
    AddSubgroup ((extendByZeroPushforward U G).obj V) :=
  if V.unop ≤ U then ⊤ else ⊥

theorem extendByZeroSubgroup_mem
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) (x : extendByZeroSubgroup U G V) :
    ((extendByZeroPushforward U G).map f).hom ((extendByZeroSubgroup U G V).subtype x) ∈
      extendByZeroSubgroup U G W := by
  by_cases hW : W.unop ≤ U
  · simp only [extendByZeroSubgroup, if_pos hW, AddSubgroup.mem_top]
  · have hV : ¬ V.unop ≤ U := fun h => hW (le_trans (leOfHom f.unop) h)
    have hx : ((extendByZeroSubgroup U G V).subtype x : (extendByZeroPushforward U G).obj V) = 0 := by
      have hx' := x.2
      simp only [extendByZeroSubgroup, if_neg hV, AddSubgroup.mem_bot] at hx'
      simpa using hx'
    simp only [hx, map_zero]
    exact zero_mem _

/-- the presheaf whose sheafification is `extendByZero U G` -/
def extendByZeroPresheaf
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (extendByZeroSubgroup U G V)
  map {V W} f := AddCommGrpCat.ofHom
    ((((extendByZeroPushforward U G).map f).hom.comp (extendByZeroSubgroup U G V).subtype).codRestrict
      (extendByZeroSubgroup U G W) (extendByZeroSubgroup_mem U G f))
  map_id := by
    intro V
    ext x
    show ((extendByZeroPushforward U G).map (𝟙 V)).hom (x : (extendByZeroPushforward U G).obj V) = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp := by
    intro V W Z f g
    ext x
    show ((extendByZeroPushforward U G).map (f ≫ g)).hom (x : (extendByZeroPushforward U G).obj V) =
      ((extendByZeroPushforward U G).map g).hom (((extendByZeroPushforward U G).map f).hom x)
    rw [CategoryTheory.Functor.map_comp]
    rfl

theorem extendByZero_eq_sheafify
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    TopCat.Sheaf.extendByZero U G =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (extendByZeroPresheaf U G) :=
  rfl

/-- the inclusion of the presheaf into `j_* G` -/
def extendByZeroPresheafι
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    extendByZeroPresheaf U G ⟶ extendByZeroPushforward U G where
  app V := AddCommGrpCat.ofHom (extendByZeroSubgroup U G V).subtype
  naturality := by
    intros V W f
    ext x
    rfl

/-- The inclusion `P ⟶ j_* G` is a monomorphism of presheaves (stated as a theorem, not an instance). -/
theorem extendByZeroPresheafι_mono
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    Mono (extendByZeroPresheafι U G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro V
  rw [AddCommGrpCat.mono_iff_injective]
  exact Subtype.val_injective

/-- the monomorphism `j_! G ⟶ j_* G` of sheaves -/
def extendByZeroToPushforward
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    TopCat.Sheaf.extendByZero U G ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (extendByZeroPresheafι U G) ≫
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G)

/-- `j_! G ⟶ j_* G` is a monomorphism of sheaves (stated as a theorem, not an instance). -/
theorem extendByZeroToPushforward_mono
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    Mono (extendByZeroToPushforward U G) := by
  unfold extendByZeroToPushforward
  haveI := extendByZeroPresheafι_mono U G
  have h1 : Mono ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (extendByZeroPresheafι U G)) := Functor.map_mono _ _
  have h2 : Mono ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G)) :=
    @IsIso.mono_of_iso _ _ _ _ _
      (isIso_sheafificationAdjunction_counit
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj G))
  exact @mono_comp _ _ _ _ _ _ h1 _ h2

/-- sections of `j_! G` over an open disjoint from `U` vanish -/
theorem subsingleton_extendByZero_obj_of_disjoint
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})
    (W : Opens X) (hW : Disjoint (U : Set X) W) :
    Subsingleton ((TopCat.Sheaf.extendByZero U G).obj.obj (op W)) := by
  haveI := extendByZeroToPushforward_mono U G
  have hm : Mono (extendByZeroToPushforward U G).hom :=
    Functor.map_mono (sheafToPresheaf _ _) (extendByZeroToPushforward U G)
  have happ := (NatTrans.mono_iff_mono_app _).mp hm (op W)
  rw [AddCommGrpCat.mono_iff_injective] at happ
  have hterm : IsTerminal (G.obj.obj (op ((Opens.map (Opens.inclusion' U)).obj W))) :=
    CategoryTheory.Sheaf.isTerminalOfBotCover G _ (fun x hx => (Set.disjoint_left.mp hW x.2 hx).elim)
  have : Subsingleton (G.obj.obj (op ((Opens.map (Opens.inclusion' U)).obj W))) :=
    AddCommGrpCat.subsingleton_of_isZero hterm.isZero
  exact @Function.Injective.subsingleton _ _ _ happ this

/-- `j_! G` restricted to an open `V` disjoint from `U` is zero (second half of Stacks 02UT) -/
theorem isZero_restrict_extendByZero_of_disjoint
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})
    (V : Opens X) (hUV : Disjoint (U : Set X) V) :
    IsZero (TopCat.Sheaf.restrict (TopCat.Sheaf.extendByZero U G) V) := by
  have hval : IsZero (TopCat.Sheaf.restrict (TopCat.Sheaf.extendByZero U G) V).obj := by
    refine Functor.isZero _ (fun W => ?_)
    have : Subsingleton ((TopCat.Sheaf.extendByZero U G).obj.obj
        (op ((Opens.isOpenEmbedding V).functor.obj W.unop))) := by
      refine subsingleton_extendByZero_obj_of_disjoint U G _ ?_
      refine Set.disjoint_left.mpr fun x hxU hxW => ?_
      obtain ⟨y, _, rfl⟩ := hxW
      exact Set.disjoint_left.mp hUV hxU y.2
    exact @AddCommGrpCat.isZero_of_subsingleton _ this
  rw [IsZero.iff_id_eq_zero] at hval ⊢
  apply (sheafToPresheaf _ _).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hval

/-- transport of morphisms through the presheaf -/
def extendByZeroPresheafMap
    {G G' : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}} (φ : G ⟶ G') :
    extendByZeroPresheaf U G ⟶ extendByZeroPresheaf U G' where
  app V := AddCommGrpCat.ofHom
    (((((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map φ).hom.app V).hom.comp
      (extendByZeroSubgroup U G V).subtype).codRestrict (extendByZeroSubgroup U G' V) (by
        intro x
        by_cases hV : V.unop ≤ U
        · simp only [extendByZeroSubgroup, if_pos hV, AddSubgroup.mem_top]
        · have hx : ((extendByZeroSubgroup U G V).subtype x : (extendByZeroPushforward U G).obj V) = 0 := by
            have hx' := x.2
            simp only [extendByZeroSubgroup, if_neg hV, AddSubgroup.mem_bot] at hx'
            simpa using hx'
          simp only [AddMonoidHom.comp_apply, hx, map_zero]
          exact zero_mem _))
  naturality := by
    intro V W f
    ext x
    refine Subtype.ext ?_
    have := congrArg (fun g => g.hom ((extendByZeroSubgroup U G V).subtype x))
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map φ).hom.naturality f)
    exact this

/-- `j_!` as a functor -/
def extendByZeroFunctor :
    CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj G := TopCat.Sheaf.extendByZero U G
  map φ := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (extendByZeroPresheafMap U φ)
  map_id := by
    intro G
    have : extendByZeroPresheafMap U (𝟙 G) = 𝟙 (extendByZeroPresheaf U G) := by
      ext V x
      refine Subtype.ext ?_
      show (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map (𝟙 G)).hom.app V).hom
        ((extendByZeroSubgroup U G V).subtype x) = (extendByZeroSubgroup U G V).subtype x
      exact (congrArg (fun m => (m.hom.app V).hom ((extendByZeroSubgroup U G V).subtype x))
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map_id G)).trans rfl
    rw [this]
    exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_id _
  map_comp := by
    intro G G' G'' φ ψ
    have : extendByZeroPresheafMap U (φ ≫ ψ) =
        extendByZeroPresheafMap U φ ≫ extendByZeroPresheafMap U ψ := by
      ext V x
      refine Subtype.ext ?_
      show (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map (φ ≫ ψ)).hom.app V).hom
        ((extendByZeroSubgroup U G V).subtype x) =
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map ψ).hom.app V).hom
          ((((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map φ).hom.app V).hom
            ((extendByZeroSubgroup U G V).subtype x))
      exact (congrArg (fun m => (m.hom.app V).hom ((extendByZeroSubgroup U G V).subtype x))
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map_comp φ ψ)).trans rfl
    rw [this]
    exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_comp _ _

theorem isZero_val_obj_of_isZero {T : Type u} [TopologicalSpace T]
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}} (hG : IsZero G)
    (V : (Opens T)ᵒᵖ) : IsZero (G.obj.obj V) := by
  have : IsZero G.obj := Functor.map_isZero (sheafToPresheaf _ _) hG
  exact (Functor.isZero_iff _).mp this V

/-- `j_!` of a zero sheaf is zero -/
theorem isZero_extendByZero_of_isZero
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}} (hG : IsZero G) :
    IsZero (TopCat.Sheaf.extendByZero U G) := by
  rw [extendByZero_eq_sheafify]
  refine Functor.map_isZero _ ?_
  rw [Functor.isZero_iff]
  intro V
  have : Subsingleton ((extendByZeroPushforward U G).obj V) :=
    AddCommGrpCat.subsingleton_of_isZero
      (isZero_val_obj_of_isZero hG (op ((Opens.map (Opens.inclusion' U)).obj V.unop)))
  exact @AddCommGrpCat.isZero_of_subsingleton _
    (inferInstanceAs (Subsingleton (extendByZeroSubgroup U G V)))

theorem extendByZeroFunctor_obj
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :
    (extendByZeroFunctor U).obj G = TopCat.Sheaf.extendByZero U G := rfl

/-- the adjunction `j^* ⊣ j_*` for the naive restriction -/
def restrictPushforwardAdjunction :
    (Opens.isOpenEmbedding U).sheafPullback AddCommGrpCat.{u} ⊣
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (Opens.inclusion' U)).ofNatIsoLeft
    ((Opens.isOpenEmbedding U).sheafPullbackIso AddCommGrpCat.{u})

/-- restriction of the constant sheaf is the constant sheaf (both are left adjoint to global sections) -/
def restrictConstantSheafNatIso :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (Opens.isOpenEmbedding U).sheafPullback AddCommGrpCat.{u} ≅
      constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} :=
  Adjunction.natIsoOfRightAdjointNatIso
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).comp
      (restrictPushforwardAdjunction U))
    (constantSheafAdj (Opens.grothendieckTopology U) AddCommGrpCat.{u} isTerminalTop)
    (Iso.refl _)

def restrictConstantSheafIso (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf.restrict ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) U ≅
      (constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}).obj A :=
  (restrictConstantSheafNatIso U).app A

end TopCat.Sheaf

end
