import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface

/-! # The value of `Φ` at a point of the section

If `Φ ∘ σ = f ∘ ρ` and `(f ∘ ρ)(y) = x`, then `Φ(σ(y)) = x`: the section `σ` carries the prescribed
point `x` into the fibre over `y` (proof of Lemma 5.1 of the paper, §5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- From `σ ≫ Φ = ρ ≫ f` and `f(ρ(y)) = x` we get `Φ(σ(y)) = x`. -/
theorem phi_sigma_eq {k : Type u} [Field k] {S : SmoothProjectiveSurface k}
    {X : SmoothProjectiveVariety k} {C C₀ : SmoothProjectiveCurve k}
    (Φ : S.toScheme ⟶ X.toScheme) (σ : C.toScheme ⟶ S.toScheme)
    (ρ : C.toScheme ⟶ C₀.toScheme) (f : C₀.toScheme ⟶ X.toScheme)
    (h : σ ≫ Φ = ρ ≫ f) (y : C.toScheme) (x : X.toScheme)
    (hy : f.base (ρ.base y) = x) : Φ.base (σ.base y) = x := by
  rw [← hy]
  simpa using congrArg (fun φ => φ.base y) h

end
