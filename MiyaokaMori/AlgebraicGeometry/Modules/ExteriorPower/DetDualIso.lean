import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankBridge
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DeterminantLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.VectorBundleDual
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.CanonicalModuleBasic

/-! # The determinant commutes with duality

For a locally free sheaf `E` of rank `n`, `det(E^∨) ≅ (det E)^∨` (from the perfect pairing
`∧^n E ⊗ ∧^n E^∨ → O_X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `det(E^∨) ≅ (det E)^∨` for a vector bundle `E`. -/
theorem VectorBundle.det_dual {k : Type*} [Field k] {X : Variety k} (E : AlgebraicGeometry.VectorBundle X) :
    Nonempty ((AlgebraicGeometry.VectorBundle.dual E).det.toModules
      ≅ AlgebraicGeometry.Scheme.Modules.dual (AlgebraicGeometry.VectorBundle.det E).toModules) := by
  let X0 : AlgebraicGeometry.Proj.SchemeOver k :=
    ⟨X.toScheme, X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩
  letI : E.toModules.IsLocallyFree := E.locallyFree
  letI : E.toModules.IsFiniteType := E.isFiniteType
  have hM : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X0 E.toModules E.rank := by
    exact AlgebraicGeometry.Scheme.Modules.isLocallyFreeRank_of_rankAtStalk_eq
      (fun x => E.rankAtStalk_eq x)
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.moduleExteriorPower_dual_iso X0 E.toModules E.rank E.rank hM
  exact ⟨e⟩

end
