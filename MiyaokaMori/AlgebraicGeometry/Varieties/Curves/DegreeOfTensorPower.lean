import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.Stacks0ayx

/-! # Degree of a tensor power of a line bundle on a curve

On a curve, `deg (L^{⊗q}) = q · deg L` for `q : ℤ` (used in the paper in the form
`deg L^{-m} = -m d_L`, so `deg L^{-q} < 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem LineBundle.degree_zpow {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (q : ℤ) : (L.zpow q).degree = q * L.degree := by
  have hadd (p q : ℤ) :
      (L.zpow (p + q)).degree = (L.zpow p).degree + (L.zpow q).degree :=
    LineBundle.degree_eq_add_of_iso_tensor (L.zpow p) (L.zpow q) (L.zpow (p + q))
      (L.zpowAddIso p q)
  have hzero : (L.zpow 0).degree = 0 := by
    have h := hadd 0 0
    simp only [zero_add] at h
    omega
  have hone : (L.zpow 1).degree = L.degree := by
    have h := LineBundle.degree_eq_add_of_iso_tensor L (LineBundle.one C.toVariety)
      (L.zpow 1) (CategoryTheory.Iso.refl _)
    rw [LineBundle.degree_one] at h
    omega
  let φ : ℤ →+ ℤ :=
    { toFun := fun p => (L.zpow p).degree
      map_zero' := hzero
      map_add' := hadd }
  change φ q = q * L.degree
  calc
    φ q = φ (q • (1 : ℤ)) := by simp
    _ = q • φ 1 := φ.map_zsmul q 1
    _ = q * L.degree := by simp [φ, hone]

end
