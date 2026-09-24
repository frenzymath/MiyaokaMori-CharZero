import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Integer tensor powers of a line bundle

The integer tensor power `L^p` of a line bundle (an unbundled `X.Modules`): for `p ≥ 0` it is
`tensorPow L p`, for `p < 0` the tensor power of the dual; packaged as the notation
`HPow X.Modules ℤ X.Modules`, so that `L ^ p` is meaningful.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Nonnegative powers are `moduleTensorPower L n`, negative powers are `moduleNegativePower L (n+1)`
   (= the tensor power of the dual `moduleSheafDual L`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.zpow {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) : ℤ → X.Modules
  | (n : ℕ) => AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n
  | Int.negSucc n => AlgebraicGeometry.Scheme.Modules.moduleNegativePower L (n + 1)

noncomputable instance {X : AlgebraicGeometry.Scheme.{u}} : HPow X.Modules ℤ X.Modules :=
  ⟨AlgebraicGeometry.Scheme.Modules.zpow⟩

end
