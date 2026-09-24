import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface

/-! # Towers of point blowups

`IsBlowupTower β` says that `β : S → W` is a composite of finitely many point blowups of smooth
projective surfaces (an inductive definition). This is the resolution `β : S → W` of
Corollary 4.3 of the paper (§4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `β : S → W` is a tower of point blowups: either the identity, or `pointBlowup.π S p ≫ g` for a tower
`g : S → W` and a closed point `p ∈ S`. -/
inductive IsBlowupTower {k : Type u} [Field k] [PerfectField k] :
    ∀ {S W : SmoothProjectiveSurface k}, (S.toScheme ⟶ W.toScheme) → Prop
  | id (W : SmoothProjectiveSurface k) : IsBlowupTower (𝟙 W.toScheme)
  | step {S W : SmoothProjectiveSurface k} (g : S.toScheme ⟶ W.toScheme)
      (hg : IsBlowupTower g) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
      IsBlowupTower (pointBlowup.π S p hp ≫ g)

end
