import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive

/-! # Tensoring with a free module of finite rank

`G ⊗ O_X^{⊕ n} ≅ G^{⊕ n}`: tensoring with the free module of rank `n` is the `n`-fold direct sum. Used in
Stacks 0AYT (`G ⊗ i^*E ≅ G ⊗ O_Z^{⊕ n} ≅ G^{⊕ n}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **`G ⊗ O^{⊕n} ≅ G^{⊕n}`** for any module `G` on a scheme `X` (in the notation of `tensor` and
`pow`: `tensor G (pow O_X n) ≅ pow G n`).

Source: Stacks 0AYT (proof, "`G ⊗ i^*E ≅ G^{⊕ n}`"); the general fact is that `⊗` is additive
(Stacks 01CA: the tensor product of sheaves of modules commutes with direct sums, being a left adjoint
of the internal Hom, Stacks 01CM).

Proof:
1. `tensor G N ≅ G ⊗ N` (`Scheme.Modules.tensorIsoTensorObj`),
   so it suffices to show `G ⊗ ⨁_{Fin n} O_X ≅ ⨁_{Fin n} G`.
2. The functor `tensorLeft G = (G ⊗ -) : X.Modules ⥤ X.Modules` is additive
   (`Scheme.Modules.tensorLeft_additive`: it preserves
   colimits, being a left adjoint, hence binary biproducts), so it preserves finite biproducts
   (Mathlib `Functor.preservesFiniteBiproductsOfAdditive`) and `Functor.mapBiproduct` gives
   `G ⊗ ⨁_{Fin n} O_X ≅ ⨁_{Fin n} (G ⊗ O_X)`.
3. `biproduct.mapIso` with the right unitor `G ⊗ O_X ≅ G` (`Scheme.Modules.unit_eq_tensorUnit` rewrites `O_X`
   to `𝟙_ X.Modules`, then `ρ_ G`) gives `⨁_{Fin n} (G ⊗ O_X) ≅ ⨁_{Fin n} G`.

Edge cases: `n = 0` — both sides are the empty biproduct (zero object), `mapBiproduct` handles it uniformly. -/
theorem AlgebraicGeometry.Scheme.Modules.nonempty_tensor_pow_unit_iso
    {X : AlgebraicGeometry.Scheme.{u}} (G : X.Modules) (n : ℕ) :
    Nonempty (G.tensor (AlgebraicGeometry.Scheme.Modules.pow (SheafOfModules.unit X.ringCatSheaf) n) ≅
      AlgebraicGeometry.Scheme.Modules.pow G n) := by
  have := AlgebraicGeometry.Scheme.Modules.tensorLeft_additive G
  refine ⟨AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj G _ ≪≫ ?_⟩
  refine ((MonoidalCategory.tensorLeft G).mapBiproduct
    (fun _ : Fin n => (show X.Modules from SheafOfModules.unit X.ringCatSheaf))) ≪≫ ?_
  refine biproduct.mapIso fun _ => ?_
  exact MonoidalCategory.whiskerLeftIso (C := X.Modules) G
      (eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) ≪≫
    MonoidalCategoryStruct.rightUnitor (C := X.Modules) G

end
