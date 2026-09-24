import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # Constancy of a morphism on a fibre component

`IsConstantOnWith Φ Γ v` says that the morphism `Φ` takes the constant value `v` on the integral curve
`Γ`: every point of `Γ` is mapped to `v`. We show that this is equivalent to `Γ.ι ≫ Φ` being a
constant morphism. Used in the chain argument of Lemma 5.1 of the paper (§5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Φ` is constant with value `v` on the integral curve `Γ ⊆ S`: every point in the image of `Γ`
is sent to `v`. -/
def IsConstantOnWith {k : Type u} [Field k] {S X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) (Γ : IntegralCurve k S.toScheme) (v : X.toScheme) : Prop :=
  ∀ p ∈ Set.range Γ.ι.base, Φ.base p = v

/-- `Φ` is constant on `Γ` with some value iff `Γ.ι ≫ Φ` is a constant morphism. -/
theorem isConstantOnWith_iff {k : Type u} [Field k] {S X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) (Γ : IntegralCurve k S.toScheme) :
    (∃ v, IsConstantOnWith Φ Γ v) ↔ IsConstantMorphism (Γ.ι ≫ Φ) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    intro q
    change Φ.base (Γ.ι.base q) = v
    exact hv _ ⟨q, rfl⟩
  · intro h
    rcases h with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    intro p hp
    obtain ⟨q, rfl⟩ := hp
    exact hv q

end
