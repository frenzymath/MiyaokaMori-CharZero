import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Quasi-coherent commutative algebras

Quasi-coherent commutative `O_X`-algebras on a scheme `X` (the input of the relative Spec).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- A quasi-coherent commutative `O_X`-algebra: a quasi-coherent module with a commutative, associative,
unital multiplication. Here `⊗`, `𝟙_`, `λ_`, `α_`, `▷`, `◁` are the monoidal structure of `X.Modules`
(`Modules.tensor` is its `tensorObj`) and `β_` is the braiding of its symmetric structure. -/
structure AlgebraicGeometry.Scheme.QCAlgebra (X : AlgebraicGeometry.Scheme.{u}) where
  carrier : X.Modules
  [quasicoherent : carrier.IsQuasicoherent]
  mul : carrier ⊗ carrier ⟶ carrier
  one : 𝟙_ X.Modules ⟶ carrier
  one_mul : (λ_ carrier).hom = (one ▷ carrier) ≫ mul
  mul_assoc : (α_ carrier carrier carrier).hom ≫ (carrier ◁ mul) ≫ mul = (mul ▷ carrier) ≫ mul
  mul_comm : (β_ carrier carrier).hom ≫ mul = mul

end
