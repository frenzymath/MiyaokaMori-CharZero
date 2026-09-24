import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Tensor products and tensor powers of global sections

The tensor product `s ⊗ t ∈ Γ(M ⊗ N)` of global sections and the tensor power `s^{⊗e} ∈ Γ(M^{⊗e})`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `s ⊗ t ∈ Γ(M ⊗ M', ⊤)`: `moduleTensorSection` (the image of `s ⊗ₜ t` in the presheaf
   tensor product under the sheafification unit; `Modules.tensor` is `moduleTensor`). -/

noncomputable def sectionTensor {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (t : (M'.val.obj (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.tensor M M').val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorSection (U := ⊤) s t

/- `s^{⊗e}`: iterate `sectionTensor` along the recursion of `tensorPow` (right multiplication:
   `tensorPow (e+1) = tensor (tensorPow e) M`). The alternative `moduleTensorPowerSection` follows the
   left-multiplication convention `moduleTensorPower (e+1) = moduleTensor M (…)`; the two tensor powers
   differ only in the order of the factors (bridged by associators/braidings); here we follow `tensorPow`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowSection {X : AlgebraicGeometry.Scheme.{u}}
    {M : X.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (e : ℕ) → ((AlgebraicGeometry.Scheme.Modules.tensorPow M e).val.obj (Opposite.op ⊤) : Type u)
  | 0 => (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))
  | e + 1 => sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e) s

end
