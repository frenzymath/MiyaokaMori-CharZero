import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackDegreeOnCurve

/-! # Pullback of nef line bundles

The pullback of a nef line bundle along a proper `k`-morphism of smooth projective varieties is nef.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pullback of a nef line bundle along a proper `k`-morphism is nef. -/
theorem IsNef.pullback {k : Type u} [Field k] [IsAlgClosed k] {S X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper Φ] {L : LineBundle X.toVariety} (hL : IsNef L) :
    IsNef (Φ ^* L) := by
  intro Γ
  obtain ⟨hconst, hnonconst⟩ := degree_pullback_restrict Φ L Γ
  by_cases hΓ : IsConstantMorphism (Γ.ι ≫ Φ)
  · rw [hconst hΓ]
  · obtain ⟨R, g, _, _, hEq⟩ := hnonconst hΓ
    have hR : 0 ≤ L ⬝ R.fundamentalClass := hL R
    rw [hEq]
    exact mul_nonneg (Int.natCast_nonneg _) hR

end
