import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Tensor product of bundled line bundles

The tensor product `L ⊗ M` of bundled line bundles: the underlying module is
`Scheme.Modules.tensor L.toModules M.toModules` (the tensor product of two line bundles is a line bundle,
Stacks 01CT), bundled into `LineBundle X` by `LineBundle.ofModules`. This is the `L.tensor M` used for
`L^{⊗q}` and `ρ^*A ⊗ L^{-q}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def LineBundle.tensor {k : Type u} [Field k] {X : Variety k} (L M : LineBundle X) :
    LineBundle X :=
  LineBundle.ofModules (AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules)

theorem LineBundle.tensor_toModules {k : Type u} [Field k] {X : Variety k} (L M : LineBundle X) :
    (L.tensor M).toModules = AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules :=
  rfl

end
