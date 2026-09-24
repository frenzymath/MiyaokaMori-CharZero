import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator

/-! # The fundamental class with rational coefficients

The fundamental class `[X]_ℚ ∈ A_{dim X}(X)_ℚ` of an integral scheme `X` with rational
coefficients (used in the proof of Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open Classical in
/-- The fundamental class `[X]_ℚ ∈ A_s(X)_ℚ` of an integral scheme `X` of dimension `s`: the class of
the cycle with coefficient `1` at the generic point (and `0` in the degenerate case where the height
of the generic point is not `s`). -/
noncomputable def AlgebraicGeometry.fundamentalClassRat (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] (s : ℕ) (hs : X.dimension = s) :
    AlgebraicGeometry.ChowGroupRat X s :=
  if h : Order.height (genericPoint X) = (s : ℕ∞) then
    AlgebraicGeometry.ChowGroupRat.of (AlgebraicGeometry.ChowGroup.mk
      ⟨Function.locallyFinsuppWithin.single (genericPoint X) (1 : ℤ), fun x hx => by
        rw [Function.locallyFinsuppWithin.single_apply] at hx
        by_cases hxe : x = genericPoint X
        · subst hxe; exact h
        · simp [hxe] at hx⟩)  -- the support is `{ξ}` and `height ξ = s`
  else 0

end
