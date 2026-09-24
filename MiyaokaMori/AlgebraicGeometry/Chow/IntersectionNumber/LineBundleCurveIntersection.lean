import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalence
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor

/-! # Intersection number of a line bundle with a one-cycle

The intersection number `L · Z ∈ ℤ` of a line bundle with a one-cycle: `deg(c₁(L) ∩ [Z])`, additive in
`Z`; it depends only on the isomorphism class of `L`, is compatible with the intersection number of
divisors (`O(D) · Z = D · Z`), and is additive under tensor products of line bundles. Numerical
equivalence in §4 of the paper is phrased with intersection numbers of line bundles; the divisor
version `intersectionNumber` is defined only for Cartier divisors, so this definition is needed.
Source: Fulton, Intersection Theory, §2.5, §2.3. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The intersection number of a line bundle with one-cycles, as an additive homomorphism:
`Z ↦ deg(c₁(L) ∩ [Z])`. -/
noncomputable def LineBundle.interHom {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} (L : LineBundle X.toVariety) :
    OneCycle X.toVariety →+ ℤ :=
  (ChowGroup.degree X).comp
    ((AlgebraicGeometry.firstChernClass L.toModules 1).comp
      AlgebraicGeometry.ChowGroup.mk)

/-- The intersection number `L ⬝ Z := deg(c₁(L) ∩ [Z])` of a line bundle with a one-cycle. -/
noncomputable def LineBundle.inter {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} (L : LineBundle X.toVariety) (Z : OneCycle X.toVariety) : ℤ :=
  L.interHom Z

/- Overloaded notation of the same shape (and precedence) as `D ⬝ Z` for divisors; for `L : LineBundle`
   it denotes `LineBundle.inter`. -/

notation:70 L:70 " ⬝ " Z:71 => LineBundle.inter L Z

/-- The intersection number depends only on the isomorphism class of the line bundle. -/
theorem LineBundle.inter_congr {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {L L' : LineBundle X.toVariety}
    (e : L.toModules ≅ L'.toModules) (Z : OneCycle X.toVariety) : L ⬝ Z = L' ⬝ Z := by
  change ChowGroup.degree X
      (AlgebraicGeometry.firstChernClass L.toModules 1 (AlgebraicGeometry.ChowGroup.mk Z)) =
    ChowGroup.degree X
      (AlgebraicGeometry.firstChernClass L'.toModules 1 (AlgebraicGeometry.ChowGroup.mk Z))
  rw [AlgebraicGeometry.firstChernClass_congr _ _ e]

/-- Compatibility with the intersection number of divisors: `O(D) ⬝ Z = D ⬝ Z`. -/
theorem CartierDivisor.lineBundle_inter {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} (D : CartierDivisor X.toVariety) (Z : OneCycle X.toVariety) :
    D.lineBundle ⬝ Z = intersectionNumber X D Z := by
  -- `capDivisor_eq_firstChernClass` (with `i = 0`), then take degrees
  change ChowGroup.degree X
      (AlgebraicGeometry.firstChernClass D.lineBundle.toModules 1 (AlgebraicGeometry.ChowGroup.mk Z)) =
    ChowGroup.degree X (capDivisor D 0 Z)
  rw [← capDivisor_eq_firstChernClass D 0 Z]

/-- Additivity in the line bundle: `N ≅ L ⊗ M ⇒ N ⬝ Z = L ⬝ Z + M ⬝ Z`. -/
theorem LineBundle.inter_tensor {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {L M N : LineBundle X.toVariety}
    (e : N.toModules ≅ AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules)
    (Z : OneCycle X.toVariety) : N ⬝ Z = L ⬝ Z + M ⬝ Z := by
  change ChowGroup.degree X
      (AlgebraicGeometry.firstChernClass N.toModules 1 (AlgebraicGeometry.ChowGroup.mk Z)) =
    ChowGroup.degree X
        (AlgebraicGeometry.firstChernClass L.toModules 1 (AlgebraicGeometry.ChowGroup.mk Z)) +
      ChowGroup.degree X
        (AlgebraicGeometry.firstChernClass M.toModules 1 (AlgebraicGeometry.ChowGroup.mk Z))
  rw [AlgebraicGeometry.firstChernClass_congr _ _ e,
    AlgebraicGeometry.firstChernClass_tensor (k := k)]
  simp only [AddMonoidHom.add_apply]
  rw [map_add]

end
