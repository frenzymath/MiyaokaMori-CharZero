import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower

/-! # Tensor powers depend only on the isomorphism class

An isomorphism `V ≅ V'` induces `V^{⊗m} ≅ V'^{⊗m}` for every `m : ℕ`.

Proof by recursion on `m`. For `m = 0`, `tensorPow V 0 = O_X = tensorPow V' 0`; take the identity.
For `m + 1`, `tensorPow V (m+1) = Modules.tensor (tensorPow V m) V`: use `tensorIsoTensorObj` to pass
from `Modules.tensor` to the monoidal `⊗` of `X.Modules`, apply `tensorIso` (functoriality of `⊗` in
isomorphisms) to the induction hypothesis and `e`, and pass back with the inverse of
`tensorIsoTensorObj`.

Source: Stacks 01CA (the tensor product is a bifunctor).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `V ≅ V'` induces `V^{⊗m} ≅ V'^{⊗m}`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowMapIso
    {X : AlgebraicGeometry.Scheme.{u}} {V V' : X.Modules} (e : V ≅ V') :
    (m : ℕ) → AlgebraicGeometry.Scheme.Modules.tensorPow V m ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow V' m
  | 0 => CategoryTheory.Iso.refl _
  | m + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e m) e ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm

end
