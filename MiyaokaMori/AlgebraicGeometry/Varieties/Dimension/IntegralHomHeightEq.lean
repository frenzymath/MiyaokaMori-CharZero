import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.IntegralHomFiberIncomparable
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SpecializingMapHeightLe

/-! # Integral morphisms preserve the height of points

An integral (in particular a finite) morphism preserves the dimension of points:
`height f(x) = height x`. Going-up (chains lift along the closed map) gives `≥`, and
incomparability (no strict specialization inside a fibre) gives `≤`.

Sources: Stacks 02R5, 02RM, 02RH, 02RT, 02S2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.height_apply_eq_of_isIntegralHom {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsIntegralHom f] (x : X) :
    Order.height (f.base x) = Order.height x := by
  refine le_antisymm
    (AlgebraicGeometry.Scheme.height_apply_le_of_specializingMap f
      f.isClosedMap.specializingMap x) ?_
  refine Order.height_le_height_apply_of_strictMono f.base (fun a b hab => ?_) x
  have hmono := f.base.hom.continuous.specialization_monotone
  refine lt_of_le_not_ge (hmono hab.le) fun hge => ?_
  have heq : f.base b = f.base a :=
    (Specializes.antisymm (hmono hab.le) hge).eq
  have := AlgebraicGeometry.IsIntegralHom.eq_of_specializes_of_eq f hab.le heq
  exact hab.ne this.symm

end
