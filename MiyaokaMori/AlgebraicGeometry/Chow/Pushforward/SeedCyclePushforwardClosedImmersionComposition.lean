import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ProperPushforward
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition

/-!
# Proper pushforward through the selected closed component

This file proves the coefficient identity for a proper map followed by the actual
closed immersion selecting the target component.  The closed immersion preserves
point-closure dimension and has residue degree one.  The proof keeps the genuine
dimension branch for the first map: if that branch fails, both sides have zero
coefficient; if it holds, the residue-field tower gives the same coefficient.

The result is independent of any stronger support-preservation structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

namespace AlgebraicGeometry.Intersection

universe u

variable {X Y Z : Scheme.{u}}

/-- A closed immersion preserves the topological dimension of every point closure. -/
theorem closedImmersion_pointClosureDimension_eq
    (i : X ⟶ Y) [IsClosedImmersion i] (x : X) :
    pointClosureDimension X x = pointClosureDimension Y (i x) := by
  have hclosure : i '' closure ({x} : Set X) = closure ({i x} : Set Y) := by
    simpa only [Set.image_singleton] using
      (i.isClosedEmbedding.closure_image_eq ({x} : Set X)).symm
  let e : closure ({x} : Set X) ≃ₜ closure ({i x} : Set Y) :=
    (i.isClosedEmbedding.isEmbedding.homeomorphImage
      (closure ({x} : Set X))).trans (Homeomorph.setCongr hclosure)
  simp only [pointClosureDimension_eq_topologicalKrullDim_closure]
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

/-- A closed immersion preserves the height of every point (`Order.height`, the `ℕ∞` form of
`closedImmersion_pointClosureDimension_eq`). -/
theorem closedImmersion_height_eq (i : X ⟶ Y) [IsClosedImmersion i] (x : X) :
    Order.height x = Order.height (i x) :=
  (pointClosureDimension_eq_pointClosureDimension_iff x (i x)).mp
    (closedImmersion_pointClosureDimension_eq i x)

/-- The closed-immersion pushforward at an image point is the source coefficient. -/
theorem closedImmersion_properPushforward_apply_image
    (i : X ⟶ Y) [IsClosedImmersion i] (α : AlgebraicCycle X ℤ) (x : X) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i α (i x) = α x := by
  have hfibre : i ⁻¹' ({i x} : Set Y) = ({x} : Set X) := by
    ext y
    change i y = i x ↔ y = x
    exact i.isClosedEmbedding.injective.eq_iff
  rw [AlgebraicGeometry.AlgebraicCycle.properPushforward_apply, hfibre, finsum_mem_singleton]
  have hd := closedImmersion_height_eq i x
  simp only [if_pos hd, closedImmersion_residueDegree_eq_one i x,
    Nat.cast_one, mul_one]

/-- Proper pushforward through an actual closed immersion composes pointwise. -/
theorem properPushforward_comp_closedImmersion
    (f : X ⟶ Y) (i : Y ⟶ Z) [IsProper f] [IsClosedImmersion i]
    (α : AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i
        (AlgebraicGeometry.AlgebraicCycle.properPushforward f α) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (f ≫ i) α := by
  ext z
  by_cases hz : z ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hz
    rw [closedImmersion_properPushforward_apply_image]
    rw [AlgebraicGeometry.AlgebraicCycle.properPushforward_apply,
      AlgebraicGeometry.AlgebraicCycle.properPushforward_apply]
    have hfibre : f ⁻¹' ({y} : Set Y) =
        (f ≫ i) ⁻¹' ({i y} : Set Z) := by
      ext x
      change f x = y ↔ i (f x) = i y
      exact i.isClosedEmbedding.injective.eq_iff.symm
    apply finsum_mem_congr hfibre
    intro x _
    by_cases hα : α x = 0
    · simp [hα]
    · by_cases hdim : Order.height x = Order.height (f x)
      · have hdim_i := closedImmersion_height_eq i (f x)
        simp [Scheme.Hom.comp_apply, hdim, hdim_i,
          closedImmersion_residueDegree_eq_one, residueDegree_comp]
      · have hdim_comp : Order.height x ≠ Order.height (i (f x)) := by
          intro h
          apply hdim
          calc
            Order.height x = Order.height (i (f x)) := h
            _ = Order.height (f x) := (closedImmersion_height_eq i (f x)).symm
        simp [hdim, hdim_comp]
  · have hi : i ⁻¹' ({z} : Set Z) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hz ⟨y, hy⟩
    have hfi' : (f ≫ i) ⁻¹' ({z} : Set Z) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hz
      refine ⟨f x, ?_⟩
      change (f ≫ i) x = z at hx
      simpa only [Scheme.Hom.comp_apply] using hx
    simp only [AlgebraicGeometry.AlgebraicCycle.properPushforward_apply, hi, hfi', finsum_mem_empty]

/-- The same composition identity on dimension-indexed cycles. -/
theorem dimensionProperPushforward_comp_closedImmersion
    (f : X ⟶ Y) (i : Y ⟶ Z) [IsProper f] [IsClosedImmersion i]
    (d : ℕ) (α : DimensionCycle X d) :
    dimensionProperPushforward i d (dimensionProperPushforward f d α) =
      dimensionProperPushforward (f ≫ i) d α := by
  apply Subtype.ext
  exact properPushforward_comp_closedImmersion f i α.1

end AlgebraicGeometry.Intersection
