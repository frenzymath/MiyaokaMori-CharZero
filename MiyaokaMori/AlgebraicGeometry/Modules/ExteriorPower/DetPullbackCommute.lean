import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleIsoOfModulesIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DeterminantLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerPullbackIso

/-! # The determinant commutes with pullback

`det(f^*E) ≅ f^*(det E)`; used in the degree identity `−K_X · f_*[C] = deg f^*T_X` of the paper. The
isomorphism is `AlgebraicGeometry.Scheme.Modules.moduleExteriorPullbackIso` (`ExteriorPowerPullbackIso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `det(f^*E) ≅ f^*(det E)` for a vector bundle `E`. -/
theorem AlgebraicGeometry.VectorBundle.det_pullback {k : Type*} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) (E : AlgebraicGeometry.VectorBundle Y) :
    Nonempty ((E.pullback f).det ≅ (E.det).pullback f) := by
  exact ⟨lineBundleIsoOfModulesIso (AlgebraicGeometry.Scheme.Modules.moduleExteriorPullbackIso f E.toModules E.rank).symm⟩

end
