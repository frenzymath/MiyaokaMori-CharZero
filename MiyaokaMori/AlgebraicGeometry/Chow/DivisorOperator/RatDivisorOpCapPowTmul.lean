import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection

/-! # Iterated caps of ℚ-divisor operators on `1 ⊗ −`

The iterated cap of the ℚ-divisor operator of a line bundle on `1 ⊗ −` is `1 ⊗ −` of the iterated cap of
the integral `c₁(L)`; after taking degrees, `ChowGroupRat.degree` becomes `ChowGroup.degreeOver`.

This transport between `ChowGroupRat = ChowGroup ⊗ ℚ` and `ChowGroup` is kept in its own module: the
comparison `RatDivisorOp.topSelfIntersection_lineBundle` between the ℚ-Chow and ℤ-Chow top
self-intersections has no Snapper/`χ` content, so `RationalTopSelfIntersection` need not import the
comparison with the Snapper intersection number (Stacks 0BFI).

Source: Fulton, Intersection Theory, §1.4, §2.5 (cap products commute with extension of coefficients).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The power of the operator of a line bundle on `1 ⊗ c` is `1 ⊗ −` of the iterated cap with the integral
`c₁(L)`. By induction on `e`; the components of `RatDivisorOp` for a line bundle are by definition the
`ratExtend` of `firstChernClass`, and `ratExtend` on `1 ⊗ c` is by definition `1 ⊗ (− c)`, so every step
is `rfl`. -/
theorem AlgebraicGeometry.capPow_ratDivisorOpOfLineBundle_tmul
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] :
    ∀ (e d : ℕ) (c : AlgebraicGeometry.ChowGroup X (d + e)),
      AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) e d
          ((1 : ℚ) ⊗ₜ[ℤ] c)
        = (1 : ℚ) ⊗ₜ[ℤ] (AlgebraicGeometry.firstChernClass.capPow L e d c)
  | 0, _, _ => rfl
  | e + 1, d, c => by
    show AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) e d
        ((AlgebraicGeometry.firstChernClass L (d + e + 1)).ratExtend ((1 : ℚ) ⊗ₜ[ℤ] c)) = _
    rw [show (AlgebraicGeometry.firstChernClass L (d + e + 1)).ratExtend ((1 : ℚ) ⊗ₜ[ℤ] c)
        = (1 : ℚ) ⊗ₜ[ℤ] (AlgebraicGeometry.firstChernClass L (d + e + 1) c) from rfl]
    exact AlgebraicGeometry.capPow_ratDivisorOpOfLineBundle_tmul L e d _

/-- Transport of the dimension index commutes with `1 ⊗ −`. -/
theorem AlgebraicGeometry.chowGroupRat_rec_one_tmul {X : AlgebraicGeometry.Scheme.{u}}
    {p q : ℕ} (h : p = q) (z : AlgebraicGeometry.ChowGroup X p) :
    (h ▸ (((1 : ℚ) ⊗ₜ[ℤ] z : TensorProduct ℤ ℚ _) : AlgebraicGeometry.ChowGroupRat X p)
        : AlgebraicGeometry.ChowGroupRat X q)
      = (((1 : ℚ) ⊗ₜ[ℤ] (cast (congrArg (AlgebraicGeometry.ChowGroup X) h) z) :
          TensorProduct ℤ ℚ _) : AlgebraicGeometry.ChowGroupRat X q) := by
  subst h
  rfl

/-- The fundamental-cycle version of the top self-intersection of a ℚ-divisor operator:
`deg_ℚ (c₁(L)_ℚ^d ∩ (1 ⊗ c)) = deg_ℤ (c₁(L)^d ∩ c)`. This is the equality between
`RatDivisorOp.topSelfIntersection Y hY (ratDivisorOpOfLineBundle L) d _` and
`AlgebraicGeometry.topSelfIntersection Y hY L` (unfold the arguments on both sides). -/
theorem AlgebraicGeometry.ratDivisorOp_capPow_degree_eq_degreeOver {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (c : AlgebraicGeometry.ChowGroup X d) :
    AlgebraicGeometry.ChowGroupRat.degree X hX
        (AlgebraicGeometry.RatDivisorOp.capPow (AlgebraicGeometry.ratDivisorOpOfLineBundle L) d 0
          ((zero_add d).symm ▸
            (((1 : ℚ) ⊗ₜ[ℤ] c : TensorProduct ℤ ℚ _) : AlgebraicGeometry.ChowGroupRat X d)))
      = (AlgebraicGeometry.ChowGroup.degreeOver k X hX
          (AlgebraicGeometry.firstChernClass.capPow L d 0
            (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add d).symm) c)) : ℚ) := by
  rw [AlgebraicGeometry.chowGroupRat_rec_one_tmul (zero_add d).symm c,
    AlgebraicGeometry.capPow_ratDivisorOpOfLineBundle_tmul L d 0,
    AlgebraicGeometry.ChowGroupRat.degree_tmul, one_mul]

end
