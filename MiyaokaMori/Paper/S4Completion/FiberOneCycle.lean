import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.DivisorToOneCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.FiberDivisorPullback

/-! # The one-cycle of a fibre

For a surjective morphism `π : S → C` from a smooth projective surface to a smooth projective curve
and a point `y ∈ C`, the fibre divisor `π^*(y)` defines a one-cycle `F_y = [π^*(y)]` on `S`. This is
the cycle `∑ mᵢ Γᵢ` of Lemma 5.1 of the paper (§5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The one-cycle `[π^*(y)]` on the surface `S` associated with the fibre divisor of `π : S → C`
over the point `y`. -/
noncomputable def fiberCycle {k : Type u} [Field k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) : OneCycle S.toVariety :=
  ⟨((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ), by
    have hmem := (fiberDivisor π hπ y).weilCycle.2
    generalize ((fiberDivisor π hπ y).weilCycle : AlgebraicGeometry.AlgebraicCycle S.toScheme ℤ) = z at hmem ⊢
    have h : S.toVariety.toScheme.dimension - 1 = 1 := by
      rw [← Variety.dim_eq_scheme_dimension, S.dim_eq_two]
    rw [h] at hmem
    exact hmem⟩

end
