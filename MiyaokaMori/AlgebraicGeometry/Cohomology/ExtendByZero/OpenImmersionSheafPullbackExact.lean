import MiyaokaMori.Prelude
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Extension by zero along an open immersion is exact

**Extension by zero along an open immersion is exact** (Stacks 03F3 / 01E1's proof; Hartshorne II
Ex. 1.19). For an open `Y ⊆ X` of a scheme, write `G := Y.ι.opensFunctor : Y.Opens ⥤ X.Opens`
(`V ↦ Y.ι ''ᵁ V`). The restriction functor `j^* := G.sheafPushforwardContinuous` (composition with
`G.op`) has the left adjoint `j_! := G.sheafPullback` (Mathlib: sheafified left Kan extension along
`G.op`). This file proves that `j_!` preserves finite limits (it preserves colimits as a left adjoint;
so `j_!` is exact).

**Proof.** `G.sheafPullback ≅ sheafToPresheaf ⋙ G.op.lan ⋙ presheafToSheaf` (Mathlib
`sheafPullbackConstruction.sheafPullbackIso`); the outer two functors preserve finite limits, so it
suffices that the presheaf-level Kan extension `G.op.lan` does. Limits of presheaves are computed
pointwise (`preservesFiniteLimits_of_evaluation`), and `(G.op.lan P)(W) = colim_{(V, W ≤ G V)} P(V)`
over the costructured-arrow category `CostructuredArrow G.op (op W)` (`lanEvaluationIsoColim`). This
index category is *empty* when `W ⊄ Y` (no `V` with `W ≤ Y.ι ''ᵁ V ≤ Y`), so the colimit is `0` and
the functor `P ↦ (G.op.lan P)(W)` is the zero functor, which preserves limits; and when `W ≤ Y` it
has the *terminal object* `V₀ := Y.ι ⁻¹ᵁ W` (indeed `W ≤ Y.ι ''ᵁ V` iff `V₀ ≤ V`), so the colimit is
evaluation at `V₀`, which preserves limits. Neither case needs flatness of `G` (which fails: `G` is
not representably flat, since the index category is empty for `W ⊄ Y`), so Mathlib's
`lan_preservesFiniteLimits_of_flat` does not apply and we redo its two-line argument case by case.

No global instance is registered; the results are theorems to be used with `haveI`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory.Limits

variable {J : Type*} [Category J] {E : Type*} [Category E]

/-- Over an index category with a terminal object `T`, `colim` is naturally evaluation at `T`. -/
def colimIsoEvaluationOfIsTerminal [HasColimitsOfShape J E] {T : J} (hT : IsTerminal T) :
    (colim : (J ⥤ E) ⥤ E) ≅ (evaluation J E).obj T :=
  NatIso.ofComponents
    (fun F => (colimit.isColimit F).coconePointUniqueUpToIso (colimitOfDiagramTerminal hT F))
    (fun {F G} φ => by
      apply colimit.hom_ext
      intro j
      have h1 : colimit.ι G j ≫
          ((colimit.isColimit G).coconePointUniqueUpToIso (colimitOfDiagramTerminal hT G)).hom =
          G.map (hT.from j) :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      have h2 : colimit.ι F j ≫
          ((colimit.isColimit F).coconePointUniqueUpToIso (colimitOfDiagramTerminal hT F)).hom =
          F.map (hT.from j) :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      simp only [colim_map, ι_colimMap_assoc, evaluation_obj_map]
      rw [h1, reassoc_of% h2]
      exact (φ.naturality (hT.from j)).symm)

/-- `colim` over an index category with a terminal object preserves finite limits. -/
theorem preservesFiniteLimits_colim_of_isTerminal [HasColimitsOfShape J E] [HasFiniteLimits E]
    {T : J} (hT : IsTerminal T) : PreservesFiniteLimits (colim : (J ⥤ E) ⥤ E) :=
  have : PreservesFiniteLimits ((evaluation J E).obj T) := ⟨fun _ _ _ => inferInstance⟩
  preservesFiniteLimits_of_natIso (colimIsoEvaluationOfIsTerminal hT).symm

/-- `colim` over an empty index category is the zero functor, hence preserves finite limits. -/
theorem preservesFiniteLimits_colim_of_isEmpty [IsEmpty J] [HasColimitsOfShape J E]
    [HasZeroObject E] [HasZeroMorphisms E] :
    PreservesFiniteLimits (colim : (J ⥤ E) ⥤ E) := by
  have hz : IsZero (colim : (J ⥤ E) ⥤ E) := by
    rw [Functor.isZero_iff]
    intro F
    refine IsInitial.isZero (IsInitial.ofUniqueHom
      (fun Z => colimit.desc F ⟨Z, ⟨fun j => isEmptyElim j, fun j => isEmptyElim j⟩⟩)
      (fun Z m => colimit.hom_ext (fun j => isEmptyElim j)))
  exact ⟨fun J' _ _ => Functor.preservesLimitsOfShape_of_isZero _ hz J'⟩

end CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (L : C ⥤ D)
  {E : Type v} [Category.{u} E] [HasColimitsOfSize.{u, u} E] [HasFiniteLimits E] [HasZeroObject E]
  [HasZeroMorphisms E]

/-- **Left Kan extension along `L` preserves finite limits** when every costructured-arrow category
`CostructuredArrow L d` is empty or has a terminal object (pointwise, the Kan extension is then `0`
or evaluation at the terminal object). -/
theorem preservesFiniteLimits_lan_of_isEmpty_or_isTerminal
    (h : ∀ d : D, IsEmpty (CostructuredArrow L d) ∨
      ∃ T : CostructuredArrow L d, Nonempty (IsTerminal T)) :
    PreservesFiniteLimits (L.lan : (C ⥤ E) ⥤ (D ⥤ E)) := by
  apply preservesFiniteLimits_of_evaluation
  intro d
  have : PreservesFiniteLimits
      ((whiskeringLeft _ _ E).obj (CostructuredArrow.proj L d) ⋙ colim) := by
    rcases h d with hd | ⟨T, ⟨hT⟩⟩
    · have := hd
      have := preservesFiniteLimits_colim_of_isEmpty (J := CostructuredArrow L d) (E := E)
      exact comp_preservesFiniteLimits _ _
    · have := preservesFiniteLimits_colim_of_isTerminal (E := E) hT
      exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (lanEvaluationIsoColim E L d).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Opens

variable {X : AlgebraicGeometry.Scheme.{u}} (Y : X.Opens)

/-- The costructured-arrow category of `G.op` at `op W` (`G = Y.ι.opensFunctor`) is empty if
`W ⊄ Y`, and has a terminal object (`V₀ = Y.ι ⁻¹ᵁ W`) if `W ≤ Y`. -/
theorem costructuredArrow_opensFunctor_op_isEmpty_or_isTerminal (d : (X.Opens)ᵒᵖ) :
    IsEmpty (CostructuredArrow Y.ι.opensFunctor.op d) ∨
      ∃ T : CostructuredArrow Y.ι.opensFunctor.op d, Nonempty (IsTerminal T) := by
  by_cases hW : d.unop ≤ Y
  · right
    have hle : d.unop ≤ Y.ι ''ᵁ (Y.ι ⁻¹ᵁ d.unop) := by
      rw [Y.ι.image_preimage_eq_opensRange_inf, Y.opensRange_ι]
      exact le_inf hW le_rfl
    refine ⟨CostructuredArrow.mk (Y := op (Y.ι ⁻¹ᵁ d.unop)) (homOfLE hle).op, ⟨?_⟩⟩
    refine IsTerminal.ofUniqueHom (fun A => ?_) (fun A m => ?_)
    · have hA : d.unop ≤ Y.ι ''ᵁ A.left.unop := leOfHom A.hom.unop
      have hV : Y.ι ⁻¹ᵁ d.unop ≤ A.left.unop := by
        have := leOfHom ((Opens.map Y.ι.base).map (homOfLE hA))
        rwa [Y.ι.preimage_image_eq] at this
      exact CostructuredArrow.homMk (homOfLE hV).op (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
    · exact CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  · left
    refine ⟨fun A => hW ?_⟩
    exact le_trans (leOfHom A.hom.unop) (Y.ι_image_le _)

/-- The presheaf-level left Kan extension along `Y.ι.opensFunctor.op` preserves finite limits. -/
theorem preservesFiniteLimits_lan_opensFunctor_op :
    PreservesFiniteLimits (Y.ι.opensFunctor.op.lan :
      ((Y : AlgebraicGeometry.Scheme.{u}).Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})) :=
  Functor.preservesFiniteLimits_lan_of_isEmpty_or_isTerminal _
    (costructuredArrow_opensFunctor_op_isEmpty_or_isTerminal Y)

/-- **`j_!` is exact**: the sheaf pullback (extension by zero) along the open immersion
`Y.ι` preserves finite limits (it preserves colimits as a left adjoint). -/
theorem preservesFiniteLimits_sheafPullback_opensFunctor :
    PreservesFiniteLimits (Y.ι.opensFunctor.sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u}))
      (Opens.grothendieckTopology X)) := by
  have := preservesFiniteLimits_lan_opensFunctor_op Y
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      Y.ι.opensFunctor AddCommGrpCat.{u}
      (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u}))
      (Opens.grothendieckTopology X)) := by
    have : PreservesFiniteLimits (Y.ι.opensFunctor.op.lan ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _).symm

end AlgebraicGeometry.Scheme.Opens

end
