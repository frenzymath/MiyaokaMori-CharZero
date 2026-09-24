import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S4Completion.ConstantOnComponent
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # Adjacent constant components take the same value

If `Φ` is constant on two fibre components `Γ`, `Γ'` that meet, then the two constant values agree
(they coincide at any common point). This is the step of the chain argument in the proof of
Lemma 5.1 of the paper (§5) that propagates the prescribed value along a chain
of constant components.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Two constant components of a fibre that meet have the same constant value. -/
theorem adjacent_constant_values_eq {k : Type u} [Field k] {S X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) {Γ Γ' : IntegralCurve k S.toScheme} {v v' : X.toScheme}
    (hv : IsConstantOnWith Φ Γ v) (hv' : IsConstantOnWith Φ Γ' v')
    (hmeet : (Set.range Γ.ι.base ∩ Set.range Γ'.ι.base).Nonempty) : v = v' := by
  obtain ⟨p, hp, hp'⟩ := hmeet
  exact (hv p hp).symm.trans (hv' p hp')

end
