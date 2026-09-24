import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # The dual of a morphism of sheaves of modules

Contravariant functoriality of the dual: a morphism `g : V ⟶ W` induces `g^∨ : W^∨ ⟶ V^∨` (where
`W^∨ = 𝓗om(W, O_X)`), obtained by currying `W^∨ ⊗ V → W^∨ ⊗ W → O_X` (apply `g`, then evaluate)
through the tensor–Hom adjunction.

Reference: Stacks 01CM (tensor–Hom adjunction).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Contravariant functoriality of the dual: `g : V ⟶ W` gives `g^∨ : W^∨ ⟶ V^∨` (`W^∨ = 𝓗om(W, O_X)`).
   Construction: `W^∨ ⊗ V --(W^∨ ◁ g)--> W^∨ ⊗ W --(evaluation internalHomEval)--> O_X`, then curry
   through the monoidal tensor–Hom adjunction `tensorObjHomEquiv` into `W^∨ ⟶ 𝓗om(V, O_X) = V^∨`. -/

/-- The dual `g^∨ : W^∨ ⟶ V^∨` of a morphism `g : V ⟶ W`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.dualMap {X : AlgebraicGeometry.Scheme.{u}}
    {V W : X.Modules} (g : V ⟶ W) :
    AlgebraicGeometry.Scheme.Modules.dual W ⟶ AlgebraicGeometry.Scheme.Modules.dual V :=
  AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv (AlgebraicGeometry.Scheme.Modules.dual W) V
      (SheafOfModules.unit X.ringCatSheaf)
    (CategoryTheory.MonoidalCategoryStruct.whiskerLeft (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.dual W) g ≫
      AlgebraicGeometry.Scheme.Modules.internalHomEval W (SheafOfModules.unit X.ringCatSheaf))

end
