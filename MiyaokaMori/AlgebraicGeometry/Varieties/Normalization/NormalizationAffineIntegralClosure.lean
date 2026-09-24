import MiyaokaMori.Prelude

/-! # Finiteness of the normalization from finiteness of integral closures on affine opens

If on every affine open the integral closure is module-finite over the base ring, then
`f.fromNormalization` is a finite morphism (via `normalizationObjIso` and the affine-local
criterion for `IsFinite`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

/-- `f.fromNormalization` is finite as soon as the integral closures over all affine opens are
module-finite. -/
theorem bridge_isFinite_fromNormalization {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (h : ∀ U : Y.affineOpens,
      letI := (f.app U.1).hom.toAlgebra
      Module.Finite Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.Scheme.Hom.fromNormalization f) := by
  constructor
  intro U hU
  letI := (f.app U).hom.toAlgebra
  have hfinite :
      (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))).Finite := by
    change Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))
    exact h ⟨U, hU⟩
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.finite
    hfinite

end
