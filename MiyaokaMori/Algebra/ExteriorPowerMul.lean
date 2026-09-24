import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Submodule

/-! # Wedge multiplication of exterior powers

The **wedge multiplication** `⋀^a M ⊗ ⋀^b M → ⋀^{a+b} M` between exterior powers of a module.

This is the algebraic core of the wedge multiplication of exterior powers of sheaves of modules:
the sheaf-level multiplication is `Module.exteriorPowerMul` on each open set, descended along
sheafification.

Reference: Bourbaki, *Algèbre* III §7 (the exterior algebra is graded, `⋀^a · ⋀^b ⊆ ⋀^{a+b}`); it is
the multiplication used in the proof of Stacks 0FJB.

Common argument for the results of this file: Mathlib **defines** `⋀[R]^n M` as the submodule
`(LinearMap.range (ExteriorAlgebra.ι R))^n` of the exterior algebra, so the multiplication of the
exterior algebra gives `⋀^a M × ⋀^b M → ExteriorAlgebra R M` with image the product of submodules
`⋀^a M * ⋀^b M`; powers of a submodule satisfy `S^a * S^b = S^{a+b}` (`pow_add`), so the image lies in
`⋀^{a+b} M` and restricting the codomain gives the required linear map. Its value on generators is
`ExteriorAlgebra.ιMulti_mul_ιMulti`:
`(m_1∧…∧m_a) · (m'_1∧…∧m'_b) = m_1∧…∧m_a∧m'_1∧…∧m'_b`, i.e. the indices are concatenated by `Fin.append`.
-/

universe u v w

open scoped TensorProduct

noncomputable section

namespace Module

/-- Composing a function into `Fin.append`: `g ∘ (u ++ v) = (g ∘ u) ++ (g ∘ v)`.

Mathlib only has right-composition versions such as `Fin.append_comp_sumElim`; this form is used
here and in the sheaf version. -/
theorem exteriorPower_comp_finAppend {α : Type v} {β : Type w} {m n : ℕ}
    (g : α → β) (u : Fin m → α) (v : Fin n → α) :
    g ∘ Fin.append u v = Fin.append (g ∘ u) (g ∘ v) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **Wedge multiplication of exterior powers** `⋀^a M ⊗_R ⋀^b M →ₗ ⋀^{a+b} M`.

It is the exterior-algebra multiplication `Submodule.mulMap` with codomain restricted to
`⋀^{a+b} M` (legitimate by `Submodule.mulMap_range` and `pow_add`); see the module docstring. -/
def exteriorPowerMul (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (a b : ℕ) : (⋀[R]^a M) ⊗[R] (⋀[R]^b M) →ₗ[R] ⋀[R]^(a + b) M :=
  LinearMap.codRestrict _ (Submodule.mulMap (⋀[R]^a M) (⋀[R]^b M)) (fun z => by
    have h : LinearMap.range (Submodule.mulMap (⋀[R]^a M) (⋀[R]^b M)) = ⋀[R]^(a + b) M := by
      rw [Submodule.mulMap_range, ← pow_add]
    exact h ▸ LinearMap.mem_range_self _ z)

/-- In the exterior algebra, wedge multiplication is the multiplication. -/
@[simp]
theorem exteriorPowerMul_tmul_coe {a b : ℕ} (x : ⋀[R]^a M) (y : ⋀[R]^b M) :
    ((exteriorPowerMul R M a b (x ⊗ₜ[R] y) : ⋀[R]^(a + b) M) : ExteriorAlgebra R M) =
      (x : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M) :=
  rfl

/-- Wedge multiplication on pure wedge generators: the indices are concatenated by `Fin.append`
(`ExteriorAlgebra.ιMulti_mul_ιMulti`). -/
@[simp]
theorem exteriorPowerMul_ιMulti {a b : ℕ} (v : Fin a → M) (w : Fin b → M) :
    exteriorPowerMul R M a b
        (exteriorPower.ιMulti R a v ⊗ₜ[R] exteriorPower.ιMulti R b w) =
      exteriorPower.ιMulti R (a + b) (Fin.append v w) := by
  apply Subtype.ext
  rw [exteriorPowerMul_tmul_coe, exteriorPower.ιMulti_apply_coe,
    exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe]
  exact ExteriorAlgebra.ιMulti_mul_ιMulti v w

/-- Two linear maps out of `⋀^a M ⊗ ⋀^b M` agreeing on tensors of pure wedges are equal.

Proof: `TensorProduct.curry` is injective; after currying, apply the universal property of the
exterior power (`exteriorPower.linearMap_ext`) twice. -/
theorem exteriorPowerMul_hom_ext {P : Type w} [AddCommGroup P] [Module R P] {a b : ℕ}
    {f g : ((⋀[R]^a M) ⊗[R] (⋀[R]^b M)) →ₗ[R] P}
    (h : ∀ (v : Fin a → M) (w : Fin b → M),
      f (exteriorPower.ιMulti R a v ⊗ₜ[R] exteriorPower.ιMulti R b w) =
        g (exteriorPower.ιMulti R a v ⊗ₜ[R] exteriorPower.ιMulti R b w)) :
    f = g := by
  apply TensorProduct.curry_injective
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w => ?_)
  exact h v w

/-- Naturality of wedge multiplication in module maps: `⋀(f)` commutes with wedge multiplication.

Proof: by `exteriorPowerMul_hom_ext` it suffices to compare on pure wedge generators, where both
sides are computed (`exteriorPower.map_apply_ιMulti`, `exteriorPowerMul_ιMulti`) as
`ιMulti (f ∘ (v ++ w))` and `ιMulti ((f ∘ v) ++ (f ∘ w))`, equal by `exteriorPower_comp_finAppend`. -/
theorem exteriorPowerMul_map {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (a b : ℕ) :
    (exteriorPower.map (a + b) f).comp (exteriorPowerMul R M a b) =
      (exteriorPowerMul R N a b).comp
        (TensorProduct.map (exteriorPower.map a f) (exteriorPower.map b f)) := by
  refine exteriorPowerMul_hom_ext fun v w => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti,
    exteriorPowerMul_ιMulti]
  rw [exteriorPower_comp_finAppend]

end Module

end
