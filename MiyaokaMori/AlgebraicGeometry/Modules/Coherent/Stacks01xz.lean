import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf

/-! # Locally free sheaves of finite type are coherent

Part of Stacks 01XZ: on a locally Noetherian scheme, a locally free sheaf of finite type is coherent.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A locally free sheaf of finite type on a locally Noetherian scheme is coherent. -/
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (M : X.Modules) [M.IsLocallyFree]
    [M.IsFiniteType] : M.IsCoherent := by
  exact ⟨SheafOfModules.instIsQuasicoherentOfIsLocallyFree
    (show SheafOfModules X.ringCatSheaf from M), inferInstance⟩

end
