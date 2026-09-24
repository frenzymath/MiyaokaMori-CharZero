import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.DegreeOfTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.NegativeDegreeNoSections
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.PullbackDegreeFiniteCover

/-! # Vanishing of the coefficients of large order

The bundle `ρ^*A⊗L^{-q}` carrying a nonzero coefficient has nonnegative degree, so `q·d_L ≤ ae`; hence all
coefficients with `q > r₀` vanish (proof of Theorem 4.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem coefficient_degree_bound {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (A : LineBundle C.toVariety) (ρ : FiniteCover k C)
    (L : LineBundle ρ.source.toVariety) (q : ℕ)
    (c : ((((LineBundle.pullback ρ.hom A).tensor
        (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u))
    (hc : c ≠ 0) :
    (q : ℤ) * L.degree ≤ A.degree * (ρ.degree : ℤ) := by
  let T := (LineBundle.pullback ρ.hom A).tensor (L.zpow (-(q : ℤ)))
  have hT : 0 ≤ T.degree := by
    by_contra hneg
    have hsub : Subsingleton
        (AlgebraicGeometry.sheafCohomology ρ.source.toScheme T.toModules 0) :=
      no_global_sections_of_degree_neg ρ.source T (lt_of_not_ge hneg)
    have hzero :
        (AlgebraicGeometry.sheafCohomologyZeroEquiv T.toModules).symm c = 0 :=
      hsub.elim _ _
    exact hc ((AlgebraicGeometry.sheafCohomologyZeroEquiv T.toModules).symm.injective
      (hzero.trans (map_zero _).symm))
  have hdeg := LineBundle.degree_eq_add_of_iso_tensor
    (LineBundle.pullback ρ.hom A) (L.zpow (-(q : ℤ))) T (CategoryTheory.Iso.refl _)
  rw [LineBundle.degree_pullback_finiteCover, LineBundle.degree_zpow] at hdeg
  dsimp only [T] at hT hdeg
  nlinarith

theorem coefficient_eq_zero_of_gt_r0 {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (A : LineBundle C.toVariety) (ρ : FiniteCover k C)
    (L : LineBundle ρ.source.toVariety) (hL : 0 < L.degree) (q : ℕ)
    (hq : A.degree * (ρ.degree : ℤ) / L.degree < (q : ℤ))
    (c : ((((LineBundle.pullback ρ.hom A).tensor
        (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    c = 0 := by
  by_contra hc
  have hbound := coefficient_degree_bound A ρ L q c hc
  have hle : (q : ℤ) ≤ A.degree * (ρ.degree : ℤ) / L.degree :=
    (Int.le_ediv_iff_mul_le hL).2 hbound
  exact (not_le_of_gt hq) hle

end
