import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.NonconstantMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme

/-! # Nonconstancy is preserved by precomposing with an isomorphism

A nonconstant morphism stays nonconstant after composition with an isomorphism (used when
reparametrizing a component by `P¹`, Lemma 5.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem nonconstant_comp_iso {k : Type u} [Field k] {W W' : AlgebraicGeometry.Scheme.{u}}
    {X : SmoothProjectiveVariety k} (g : W' ≅ W) {h : W ⟶ X.toScheme}
    (hh : ¬ IsConstantMorphism h) : ¬ IsConstantMorphism (g.hom ≫ h) := by
  rintro ⟨v, hv⟩
  exact hh ⟨v, fun w => by simpa using hv (g.inv.base w)⟩

end
