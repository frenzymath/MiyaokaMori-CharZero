import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme

/-! # Top self-intersection of a line bundle

The top self-intersection `(L^d) = deg(c_1(L)^d ∩ [X]) ∈ ℤ` of an invertible sheaf on a scheme `X`
proper over `k` of dimension `d = X.dimension`: cap the Chow class of the fundamental cycle `d` times
with `c_1(L)` and take the degree of the resulting zero-dimensional Chow class. `X` need not be
integral (the fundamental cycle carries the lengths of the components as multiplicities). Used for
the fiber degree `v_k` in Proposition 2.4 of the paper. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `e`-fold iterated cap with `c_1(L)`: `A_{d+e}(X) → A_d(X)`, defined by recursion on `e`
(the target `ChowGroup X (d + e + 1 - 1)` of `firstChernClass L (d + e + 1)` is definitionally
`ChowGroup X (d + e)`). -/
noncomputable def AlgebraicGeometry.firstChernClass.capPow {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] : (e d : ℕ) →
    AlgebraicGeometry.ChowGroup X (d + e) →+ AlgebraicGeometry.ChowGroup X d
  | 0, _ => AddMonoidHom.id _
  | e + 1, d => (AlgebraicGeometry.firstChernClass.capPow L e d).comp
      (AlgebraicGeometry.firstChernClass L (d + e + 1))

/-- The top self-intersection `(L^d) = deg(c_1(L)^d ∩ [X])` of a line bundle `L` on a scheme `X`
proper over `k`, where `d = X.dimension`. -/
noncomputable def AlgebraicGeometry.topSelfIntersection {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (L : X.Modules) [L.IsLineBundle] : ℤ :=
  haveI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  haveI : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  AlgebraicGeometry.ChowGroup.degreeOver k X hX
    (AlgebraicGeometry.firstChernClass.capPow L X.dimension 0
      (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add X.dimension).symm)
        (X.fundamentalChowClass X.dimension)))

end
