import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection

/-! # Nef line bundles

A line bundle on a smooth projective variety is nef if its intersection number with every integral
curve is nonnegative (used for `A_S` in the proof of Lemma 5.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A line bundle `L` is nef if `L · Γ ≥ 0` for every integral curve `Γ`. -/
def IsNef {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    (L : LineBundle X.toVariety) : Prop :=
  ∀ Γ : IntegralCurve k X.toScheme, 0 ≤ L ⬝ Γ.fundamentalClass

/-- Being nef is invariant under isomorphism of the underlying modules. -/
theorem IsNef.of_iso {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    {L L' : LineBundle X.toVariety} (e : L.toModules ≅ L'.toModules) (hL : IsNef L) : IsNef L' := by
  intro Γ
  have heq := LineBundle.inter_congr e Γ.fundamentalClass
  rw [← heq]
  exact hL Γ

end
