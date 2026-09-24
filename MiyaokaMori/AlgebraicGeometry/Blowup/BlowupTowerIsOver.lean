import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface

/-! # A tower of point blowups is a `k`-morphism

If `IsBlowupTower β`, then `β` is compatible with the structure morphisms to `Spec k`: each step
`pointBlowup.π` is a `k`-morphism by the definition of the `k`-structure on the blowup, and identities
and composites of `k`-morphisms are `k`-morphisms.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A tower of point blowups is a morphism over `Spec k`: the `k`-structure of `pointBlowup` is by
definition `π ≫ (S ↘ Spec k)`, so each `π` is a `k`-morphism (`rfl`), and the property is preserved by
identities and composition. -/
theorem IsBlowupTower.isOver {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    {β : S.toScheme ⟶ W.toScheme} (hβ : IsBlowupTower β) :
    β.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  induction hβ with
  | id W => exact ⟨CategoryTheory.Category.id_comp _⟩
  | step g hg p hp ih =>
    have := ih
    have : (pointBlowup.π _ p hp).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    infer_instance

end
