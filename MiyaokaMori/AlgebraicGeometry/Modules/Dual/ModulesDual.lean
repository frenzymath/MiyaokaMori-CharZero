import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom

/-! # The dual of a sheaf of modules

The dual `V^∨ = Hom_{O_X}(V, O_X)` of a sheaf of modules, used for the total space and
projectivization constructions of §2 of the paper and for `T_X = Ω_X^∨` (§1). For `E` locally free
of finite rank, `E^∨` is locally free of the same rank (`SheafDualLocallyFree`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The dual sheaf `V^∨ = Hom_{O_X}(V, O_X)`: the sheafification of the presheaf of compatible families
of local functionals (`moduleSheafDual`). It is definitionally equal to `Modules.internalHom V O_X`
(`dual_eq_internalHom`), and the negative powers of `Modules.zpow` are built from it. The
isomorphism with the direct (non-sheafified) construction `dualSheaf` is `dualSheafIsoOld`
(`DualSheafOld`); the dual of a line bundle is a line bundle by `moduleSheafDual_isLineBundle`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.dual {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) : X.Modules :=
  AlgebraicGeometry.Scheme.Modules.moduleSheafDual V

end
