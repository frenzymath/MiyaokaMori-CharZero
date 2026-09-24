import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPreservesColimits
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseSubalgebra

/-! # Veronese generation for multiples: the core argument

Statement: if the `m`-th Veronese subalgebra of a graded algebra is generated in degree one, then so
is the Veronese subalgebra of any multiple `c * m` (also for `c = 0`: then all components are `S_0`
and the multiplication `S_0 ⊗ S_0 → S_0` is an epimorphism by `one_mul`).

Proof (everything is reduced to composites and factors of epimorphisms, without constructing a
"block product" isomorphism):
1. For any graded algebra `T`: if `T_1^{⊗(m+1)} → T_{m+1}` is epi, so is its last factor
   `T_m ⊗ T_1 → T_{m+1}` (`epi_of_epi`).
2. For `T` generated in degree one, induction on `n` shows `T_m ⊗ T_n → T_{m+n}` is epi for all
   `m, n`: `n = 0` by `one_mul` + `mul_comm`; `n → n+1` by `mul_assoc`:
   `α ≫ (T_m ◁ mul n 1) ≫ mul m (n+1) = (mul m n ▷ T_1) ≫ mul (m+n) 1 ≫ eqToHom`, whose right side
   is a composite of epimorphisms (tensoring preserves epimorphisms, `tensorRight_preservesEpimorphisms`),
   so the last factor `mul m (n+1)` of the left side is epi.
3. Conversely, for any graded algebra `V`: if all `V_ℓ ⊗ V_1 → V_{ℓ+1}` are epi, then `V` is generated
   in degree one (induction on `ℓ`, with `one_mul` for `ℓ = 1`).
4. Take `T = S^{(m)}` and `V = S^{(cm)}`: `V_ℓ ⊗ V_1 → V_{ℓ+1}` is `S_{(ℓc)m} ⊗ S_{cm} → S_{(ℓc+c)m}`
   (up to an `eqToHom` on the index), which is epi by step 2 (`a = ℓc`, `b = c`).

Source: Lemma 2.2 of the paper (the standard Veronese generation argument).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- `S_0 ⊗ S_m → S_m` is an epimorphism: composed with `S.one ▷ S_m` it is an isomorphism (`one_mul`). -/
theorem epi_mul_zero_left (m : ℕ) : Epi (S.mul 0 m) := by
  have : Epi ((S.one ▷ S.part m) ≫ S.mul 0 m) := by
    rw [S.one_mul m]; infer_instance
  exact epi_of_epi (S.one ▷ S.part m) (S.mul 0 m)

/-- `S_m ⊗ S_0 → S_m` is an epimorphism (reduced to `epi_mul_zero_left` by `mul_comm`). -/
theorem epi_mul_zero_right (m : ℕ) : Epi (S.mul m 0) := by
  have := S.epi_mul_zero_left m
  have : Epi ((β_ (S.part 0) (S.part m)).hom ≫ S.mul m 0) := by
    rw [S.mul_comm 0 m]; infer_instance
  exact epi_of_epi (β_ (S.part 0) (S.part m)).hom (S.mul m 0)

/-- If `S_1^{⊗(m+1)} → S_{m+1}` is epi, then so is its last factor `S_m ⊗ S_1 → S_{m+1}`. -/
theorem epi_mul_one_of_epi_mulPowOne_succ (m : ℕ) [h : Epi (S.mulPowOne (m + 1))] :
    Epi (S.mul m 1) := by
  have : Epi ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) m) (S.part 1)).hom ≫
      (S.mulPowOne m ▷ S.part 1) ≫ S.mul m 1) := h
  have := epi_of_epi (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) m) (S.part 1)).hom
      ((S.mulPowOne m ▷ S.part 1) ≫ S.mul m 1)
  exact epi_of_epi (S.mulPowOne m ▷ S.part 1) (S.mul m 1)

/-- In a graded algebra generated in degree one, every multiplication `S_m ⊗ S_n → S_{m+n}` is an
epimorphism. -/
theorem epi_mul_of_generatedInDegreeOne (hS : S.GeneratedInDegreeOne) (m n : ℕ) :
    Epi (S.mul m n) := by
  induction n generalizing m with
  | zero => exact S.epi_mul_zero_right m
  | succ n ih =>
    have : Epi (S.mulPowOne (m + n + 1)) := hS _ (Nat.succ_pos _)
    have : Epi (S.mul (m + n) 1) := S.epi_mul_one_of_epi_mulPowOne_succ (m + n)
    have : Epi (S.mul m n) := ih m
    have : Epi (S.mul m n ▷ S.part 1) := by
      exact (MonoidalCategory.tensorRight (S.part 1)).map_epi (S.mul m n)
    have : Epi ((α_ (S.part m) (S.part n) (S.part 1)).hom ≫
        (S.part m ◁ S.mul n 1) ≫ S.mul m (n + 1)) := by
      rw [S.mul_assoc m n 1]; infer_instance
    have := epi_of_epi (α_ (S.part m) (S.part n) (S.part 1)).hom
      ((S.part m ◁ S.mul n 1) ≫ S.mul m (n + 1))
    exact epi_of_epi (S.part m ◁ S.mul n 1) (S.mul m (n + 1))

/-- If all `S_ℓ ⊗ S_1 → S_{ℓ+1}` are epi, then `S` is generated in degree one. -/
theorem generatedInDegreeOne_of_epi_mul_one (h : ∀ ℓ, Epi (S.mul ℓ 1)) :
    S.GeneratedInDegreeOne := by
  intro ℓ hℓ
  induction ℓ with
  | zero => exact absurd hℓ (Nat.lt_irrefl 0)
  | succ ℓ ih =>
    change Epi ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part 1) ℓ) (S.part 1)).hom ≫
      (S.mulPowOne ℓ ▷ S.part 1) ≫ S.mul ℓ 1)
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · have : Epi ((S.one ▷ S.part 1) ≫ S.mul 0 1) := by
        rw [S.one_mul 1]; infer_instance
      exact epi_comp' (IsIso.epi_of_iso _) this
    · have := ih hpos
      have := h ℓ
      have : Epi (S.mulPowOne ℓ ▷ S.part 1) := by
        exact (MonoidalCategory.tensorRight (S.part 1)).map_epi (S.mulPowOne ℓ)
      infer_instance

/-- If the Veronese subalgebra is generated in degree one, then every `S_{a m} ⊗ S_{b m} → S_{a m + b m}`
is an epimorphism. -/
theorem epi_mul_of_veronese_generatedInDegreeOne (m : ℕ)
    (hS : (S.veronese m).GeneratedInDegreeOne) (a b a' b' : ℕ) (ha : a = a' * m) (hb : b = b' * m) :
    Epi (S.mul a b) := by
  subst ha hb
  have h := (S.veronese m).epi_mul_of_generatedInDegreeOne hS a' b'
  change Epi (S.mul (a' * m) (b' * m) ≫ eqToHom (congrArg S.part (add_mul a' b' m).symm)) at h
  have := h
  have : Epi ((S.mul (a' * m) (b' * m) ≫ eqToHom (congrArg S.part (add_mul a' b' m).symm)) ≫
      eqToHom (congrArg S.part (add_mul a' b' m))) := epi_comp _ _
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using this

end AlgebraicGeometry.Scheme.GradedQCAlgebra

theorem veronese_generatedInDegreeOne_of_veronese
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m c : ℕ)
    (hS : (S.veronese m).GeneratedInDegreeOne) :
    (S.veronese (c * m)).GeneratedInDegreeOne := by
  apply AlgebraicGeometry.Scheme.GradedQCAlgebra.generatedInDegreeOne_of_epi_mul_one
  intro ℓ
  change Epi (S.mul (ℓ * (c * m)) (1 * (c * m)) ≫
    eqToHom (congrArg S.part (add_mul ℓ 1 (c * m)).symm))
  have : Epi (S.mul (ℓ * (c * m)) (1 * (c * m))) :=
    S.epi_mul_of_veronese_generatedInDegreeOne m hS _ _ (ℓ * c) c (Nat.mul_assoc ℓ c m).symm
      (Nat.one_mul (c * m))
  infer_instance

end
