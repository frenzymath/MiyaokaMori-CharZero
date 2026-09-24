import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveStalkDVR
import MiyaokaMori.RingTheory.OrderOfVanishing.NormalDimensionOneDvr
import MiyaokaMori.AlgebraicGeometry.Divisors.OrdNonnegOfRegularX
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.CurveStalkRamification

/-! # Ramification index of a finite cover of curves

The ramification index `e_y(η) := ord_y (η^* ϖ_z)` of a finite cover of curves `η` at a point
`y`, where `ϖ_z` is a local parameter at `z = η(y)`. The definition uses Mathlib's
`Ideal.ramificationIdx` and does not depend on a choice of local parameter; the formula in terms
of a local parameter is `ramificationIndex_eq_ord`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `e_y(η)`: the ramification index of `y` over `η(y)` under the stalk map
`η^# : O_{C,η(y)} → O_{C',y}` (Mathlib `Ideal.ramificationIdx`, the length of
`O_{C',y} / m_{η(y)} O_{C',y}`; when both stalks are DVRs this is `ord_y (η^* ϖ_{η(y)})`, see
`ramificationIndex_eq_ord`). At non-closed points it is `0` by convention. -/

noncomputable def ramificationIndex {k : Type u} [Field k] {Ct Ct' : SmoothProjectiveCurve k}
    (η : Ct'.toScheme ⟶ Ct.toScheme) (y : Ct'.toScheme) : ℕ := by
  classical
  exact if IsClosed ({y} : Set Ct'.toScheme) then
    letI : Algebra (Ct.toScheme.presheaf.stalk (η.base y)) (Ct'.toScheme.presheaf.stalk y) :=
      (η.stalkMap y).hom.toAlgebra
    Ideal.ramificationIdx (IsLocalRing.maximalIdeal (Ct'.toScheme.presheaf.stalk y))
      (Ct.toScheme.presheaf.stalk (η.base y))
  else 0

/-- `e_y(η) = ord_y (η^* ϖ)` for a local parameter `ϖ` at `η(y)`. -/
theorem ramificationIndex_eq_ord {k : Type u} [Field k] {Ct Ct' : SmoothProjectiveCurve k}
    (η : Ct'.toScheme ⟶ Ct.toScheme) [AlgebraicGeometry.IsFinite η]
    (hsurj : Function.Surjective η.base) (y : Ct'.toScheme) (hy : IsClosed ({y} : Set Ct'.toScheme))
    (ϖ : Ct.toScheme.functionField) (hϖ : Ct.toScheme.ord ϖ (η.base y) = 1) :
    (ramificationIndex η y : ℤ) = Ct'.toScheme.ord (pullbackFunction η ϖ) y := by
  have hdom : AlgebraicGeometry.IsDominant η := ⟨hsurj.denseRange⟩
  have hgen : η.base (genericPoint Ct'.toScheme) = genericPoint Ct.toScheme :=
    AlgebraicGeometry.Scheme.dominantMap_genericPoint η
  have hyc : Order.coheight y = 1 := Ct'.coheight_eq_one_of_isClosed y hy
  have hzcl : IsClosed ({η.base y} : Set Ct.toScheme) := by
    have := η.isClosedMap _ hy
    rwa [Set.image_singleton] at this
  have hzc : Order.coheight (η.base y) = 1 :=
    Ct.coheight_eq_one_of_isClosed _ hzcl
  letI : Algebra (Ct.toScheme.presheaf.stalk (η.base y))
      (Ct'.toScheme.presheaf.stalk y) := (η.stalkMap y).hom.toAlgebra
  letI : IsDiscreteValuationRing (Ct'.toScheme.presheaf.stalk y) :=
    Ct'.isDiscreteValuationRing_stalk y hyc
  letI : IsDiscreteValuationRing (Ct.toScheme.presheaf.stalk (η.base y)) :=
    Ct.isDiscreteValuationRing_stalk _ hzc
  have hϖ0 : ϖ ≠ 0 := by
    intro hϖ0
    subst hϖ0
    simp at hϖ
  have hkey := AlgebraicGeometry.Divisors.CurveStalkRamification.ord_pullback η y hyc hzc hϖ0
  rw [← pullbackFunctionHom_apply η hgen ϖ]
  simp only [ramificationIndex, if_pos hy]
  change (Ideal.ramificationIdx (IsLocalRing.maximalIdeal
      (Ct'.toScheme.presheaf.stalk y))
      (Ct.toScheme.presheaf.stalk (η.base y)) : ℤ) =
    Ct'.toScheme.ord (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η ϖ) y
  rw [hkey]
  norm_num [hϖ]

end
