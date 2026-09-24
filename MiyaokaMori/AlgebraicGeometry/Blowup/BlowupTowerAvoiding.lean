import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ClosedPoint
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface

/-! # Towers of point blowups with centres avoiding an open set

A tower of point blowups whose centres avoid an open set `U`: each step blows up a closed point whose
image in the original surface does not lie in `U` (the closed points "not lying over `U`" of
Stacks 0C5H). This is the resolution of Corollary 4.3 of the paper (§4), whose
centres lie away from the zero section.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `g : S → W` is a sequence of blowups of closed points whose images in `W` lie in `Uᶜ`, i.e. avoid `U`.
Each step is characterised by the universal property `IsBlowup (pointIdeal Y c) b` (so the definition is
insensitive to the choice of the blowup up to isomorphism), and the intermediate objects are arbitrary
schemes. -/
def IsBlowupTowerAvoiding {k : Type u} [Field k] {S W : SmoothProjectiveSurface k}
    (g : S.toScheme ⟶ W.toScheme) (U : Set W.toScheme) : Prop :=
  MiyaokaMori.Statement.IsPointBlowupSequenceOver W.toScheme Uᶜ g

end
