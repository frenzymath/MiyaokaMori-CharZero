import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.RegularScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.RingTheory.OrderOfVanishing.NormalDimensionOneDvr

/-! # Normal schemes of dimension at most one are regular (Stacks 0BX2)

Stacks 0BX2: a locally Noetherian normal scheme of dimension `≤ 1` is regular.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 0BX2: a locally Noetherian normal scheme of dimension `≤ 1` is regular. -/
theorem AlgebraicGeometry.Scheme.isRegular_of_isNormal_of_dim_le_one (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] [X.IsNormal] (h : topologicalKrullDim X ≤ 1) :
    X.IsRegular := by
  have hkrull : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact h
  constructor
  intro x
  have hx : Order.coheight x ≤ 1 :=
    WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans hkrull)
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hx
  have : IsDomain (X.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.IsNormal.isDomain x
  have : IsIntegrallyClosed (X.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.IsNormal.integrallyClosed x
  by_cases hfield : IsField (X.presheaf.stalk x)
  · let := hfield.toField
    infer_instance
  · have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      isDiscreteValuationRing_of_isIntegrallyClosed_of_dim_one
        (X.presheaf.stalk x) inferInstance hfield
    infer_instance

end
