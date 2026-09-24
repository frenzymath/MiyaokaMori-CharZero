import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.Paper.S4Completion.FiberOneCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FibersNumericallyEquivalent
import MiyaokaMori.Paper.S4Completion.GeneralFiberDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntersectionLinear
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntersectionNumeqInvariant

/-! # The special-fibre degree identity

Equation (5.1) of the paper (§5, Lemma 5.1): if the fibre cycle
over `y` decomposes as `∑ᵢ mᵢ Γᵢ`, then `∑ᵢ mᵢ (A_S · Γᵢ) = A_S · F_{y₀}` for any other closed point `y₀`,
because all fibres of `π_S` are numerically equivalent. The right-hand side is `d_F`; its positivity is
proved separately in `NefPullbackAmple`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `∑ᵢ mᵢ (A · Γᵢ) = A · [π^*(y₀)]` when the fibre cycle over `y` is `∑ᵢ mᵢ [Γᵢ]`: intersection numbers
are additive, and fibres over closed points are numerically equivalent. -/
theorem special_fiber_degree {k : Type u} [Field k] [IsAlgClosed k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme)
    [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] (hπ : AlgebraicGeometry.Surjective π)
    (A : LineBundle S.toVariety) (y y₀ : C.toScheme)
    (hy : IsClosed ({y} : Set C.toScheme)) (hy₀ : IsClosed ({y₀} : Set C.toScheme))
    {ι : Type} [Fintype ι] {m : ι → ℕ} {Γ : ι → IntegralCurve k S.toScheme}
    (hdec : fiberCycle π hπ y = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass) :
    ∑ i, (m i : ℤ) * (A ⬝ (Γ i).fundamentalClass) = fiberDegree π hπ A y₀ := by
  have hsum := inter_sum (X := S.toSmoothProjectiveVariety) A (Finset.univ : Finset ι)
    (fun i => (m i : ℤ)) Γ
  have hnum := fibers_numEquiv π hπ y y₀ hy hy₀
  have hinter := inter_eq_of_numEquiv A hnum
  calc
    ∑ i, (m i : ℤ) * (A ⬝ (Γ i).fundamentalClass) =
        A ⬝ (∑ i, (m i : ℤ) • (Γ i).fundamentalClass) := by
      simpa using hsum.symm
    _ = A ⬝ fiberCycle π hπ y := by rw [hdec]
    _ = A ⬝ fiberCycle π hπ y₀ := hinter
    _ = fiberDegree π hπ A y₀ := rfl

end
