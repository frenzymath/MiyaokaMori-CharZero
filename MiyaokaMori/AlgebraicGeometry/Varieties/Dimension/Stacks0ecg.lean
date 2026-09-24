import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.IntegralHomHeightEq

/-! # Integral morphisms and dimension (Stacks 0ECG)

An integral morphism does not raise the dimension, and an integral surjective morphism preserves
it (Stacks 0ECG).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The Krull dimension of the underlying space of a scheme (specialization preorder) is the
topological Krull dimension. -/
private theorem krullDim_scheme_eq_topologicalKrullDim (X : AlgebraicGeometry.Scheme.{u}) :
    Order.krullDim X = topologicalKrullDim X :=
  (Order.krullDim_eq_of_orderIso
    (@irreducibleSetEquivPoints X _ _ _ : IrreducibleCloseds X ≃o X)).symm

/-- An integral morphism does not raise the dimension: `dim X ≤ dim Y`. -/
theorem AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [← krullDim_scheme_eq_topologicalKrullDim, ← krullDim_scheme_eq_topologicalKrullDim,
    Order.krullDim_eq_iSup_height]
  refine iSup_le fun x => ?_
  rw [← AlgebraicGeometry.Scheme.height_apply_eq_of_isIntegralHom f x]
  exact Order.height_le_krullDim _

/-- An integral surjective morphism preserves the dimension. -/
theorem AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsIntegralHom f]
    [AlgebraicGeometry.Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  refine le_antisymm (AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom f) ?_
  rw [← krullDim_scheme_eq_topologicalKrullDim, ← krullDim_scheme_eq_topologicalKrullDim,
    Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  rw [AlgebraicGeometry.Scheme.height_apply_eq_of_isIntegralHom f x]
  exact Order.height_le_krullDim _

end
