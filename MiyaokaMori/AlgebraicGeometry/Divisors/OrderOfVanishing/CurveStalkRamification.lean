import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.CurveStalkFunctionField
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.CurveStalkValuation
import MiyaokaMori.RingTheory.OrderOfVanishing.DVRRamification

/-!
# Ramification of the canonical stalk valuations along a dominant morphism

For the same dominant morphism of integral schemes, the actual local-ring map
induces the already constructed `dominantFunctionFieldMap`. When both stalks are
DVRs, their canonical fraction-field orders scale by Mathlib's actual local
`Ideal.ramificationIdx`. At codimension-one points of locally Noetherian schemes
this gives the corresponding formula for `Scheme.ord` and the complete
`CurveStalkValuation.valuation`, including the infinite value of zero.

This is the geometric order formula `ord_y(η^*ψ) = e_y(η) ord_z(ψ)` used in the proof of Lemma 3.1 of the paper. The full
`WithTop.map` conclusion is the field-element hypothesis required by
`WeightedJets.weightedOrder_ramified_pullback`. The actual index is strictly
positive and can therefore be packaged as a positive natural by the consumer.

No other valuation, function field or numerical ramification index is defined.
The algebra on the two stalks is explicitly induced by this morphism; the proof
uses its already established scalar towers. Neither finiteness of the morphism
nor module finiteness of its stalk maps is assumed. Deriving the DVR and
codimension-one hypotheses from smooth curves, and constructing the prescribed
cover, are separate geometric tasks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace AlgebraicGeometry.Divisors.CurveStalkRamification

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f] (x : X)

/-- The named algebra on the actual stalks has a local structure map. -/
theorem stalkMap_isLocalHom :
    letI := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
    IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
  change IsLocalHom (f.stalkMap x).hom
  infer_instance

variable [IsDiscreteValuationRing (X.presheaf.stalk x)]
  [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]

/-- The ramification index of this morphism's actual map of DVR stalks is positive. -/
theorem ramificationIdx_pos :
    letI := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
    0 < (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
      (Y.presheaf.stalk (f x)) := by
  let := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
  have := stalkMap_isLocalHom f x
  exact MiyaokaMori.RingTheory.DVRRamification.ramificationIdx_pos (AlgebraicGeometry.Scheme.dominant_stalkMap_injective f x)

/-- Pullback along the canonical function-field map scales the actual DVR orders. -/
theorem ordFrac_pullback (a : Y.functionField) :
    letI := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
    Ring.ordFrac (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f a) =
      Ring.ordFrac (Y.presheaf.stalk (f x)) a ^
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
          (Y.presheaf.stalk (f x)) := by
  let := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
  let := AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra f
  let := AlgebraicGeometry.Scheme.sourceStalkFunctionFieldAlgebra f x
  have := stalkMap_isLocalHom f x
  have := AlgebraicGeometry.Scheme.sourceStalk_functionField_isScalarTower f x
  have := AlgebraicGeometry.Scheme.sourceStalk_targetStalk_isScalarTower f x
  exact MiyaokaMori.RingTheory.DVRRamification.ordFrac_algebraMap
    (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x)
    (K := Y.functionField) (L := X.functionField)
    (AlgebraicGeometry.Scheme.dominant_stalkMap_injective f x) a

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- For a nonzero rational function, geometric order scales by the same local index. -/
theorem ord_pullback (hx : coheight x = 1) (hy : coheight (f x) = 1)
    {a : Y.functionField} (ha : a ≠ 0) :
    letI := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
    X.ord (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f a) x =
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
        (Y.presheaf.stalk (f x)) : ℤ) * Y.ord a (f x) := by
  let := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
  have hfa : AlgebraicGeometry.Scheme.dominantFunctionFieldMap f a ≠ 0 := by
    intro h
    apply ha
    exact (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.injective (by simpa using h)
  apply (Scheme.ord_eq_iff hx hfa).mpr
  change Ring.ordFrac (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f a) = _
  rw [ordFrac_pullback f x]
  have haord : Ring.ordFrac (Y.presheaf.stalk (f x)) a =
      WithZero.exp (Y.ord a (f x)) :=
    (Scheme.ord_eq_iff hy ha).mp rfl
  rw [haord, ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, WithZero.exp_eq_coe_ofAdd]

variable (hx : coheight x = 1) (hy : coheight (f x) = 1)

/-- The canonical additive valuation scales on every function, with zero still infinite. -/
theorem valuation_pullback (a : Y.functionField) :
    letI := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
    CurveStalkValuation.valuation X x hx (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f a) =
      WithTop.map (fun m : ℤ ↦
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
          (Y.presheaf.stalk (f x)) : ℤ) * m)
        (CurveStalkValuation.valuation Y (f x) hy a) := by
  let := AlgebraicGeometry.Scheme.morphismStalkAlgebra f x
  by_cases ha : a = 0
  · simp [ha]
  have hfa : AlgebraicGeometry.Scheme.dominantFunctionFieldMap f a ≠ 0 := by
    intro h
    apply ha
    exact (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.injective (by simpa using h)
  rw [CurveStalkValuation.valuation_of_ne_zero X x hx hfa,
    CurveStalkValuation.valuation_of_ne_zero Y (f x) hy ha,
    ord_pullback f x hx hy ha]
  rfl

end AlgebraicGeometry.Divisors.CurveStalkRamification
