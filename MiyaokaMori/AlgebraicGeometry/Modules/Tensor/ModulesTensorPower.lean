import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Tensor powers of a sheaf of modules

The tensor power `V^{⊗e}` of a sheaf of modules (used to interpret homogeneous equations of degree
`e` as sections of `A^{⊗e}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `e`-th tensor power `V^{⊗e}`, defined recursively: `V^{⊗0} = O_X` and
`V^{⊗(e+1)} = V^{⊗e} ⊗ V`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPow {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | (e + 1) => AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow V e) V

end
