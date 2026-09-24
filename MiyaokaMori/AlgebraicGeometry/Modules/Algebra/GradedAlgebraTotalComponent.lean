import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra

/-! # The component formula for the multiplication of the total algebra

The component formula for the multiplication of the total algebra `⊕_m S_m` of a graded
quasi-coherent algebra: on the `(m, n)` component it is `S.mul m n` followed by the inclusion of the
`(m+n)`-th summand,
  `(Sigma.ι S.part m ⊗ₘ Sigma.ι S.part n) ≫ totalMul S = S.mul m n ≫ Sigma.ι S.part (m + n)`.
Together with the extension lemma `tensorObj_sigma_hom_ext` (morphisms out of `(∐ F) ⊗ (∐ G)` are
determined by their restrictions along `Sigma.ι F i ⊗ₘ Sigma.ι G j`) this characterises `totalMul`.

Proof. `totalMul` is defined by double currying: `totalMul = curry⁻¹ (Sigma.desc (fun m ↦ curry (row m)))`
with `row m = β ≫ curry⁻¹ (Sigma.desc (fun n ↦ curry (β ≫ mul m n ≫ ι_{m+n})))`, where `curry` is the
tensor–Hom adjunction `tensorObjHomEquiv` (`totalCurry` is the same definition). `curry` is natural in
the first variable (`tensorObjHomEquiv_naturality_left`), so `(a ▷ G) ≫ curry⁻¹ D = curry⁻¹ (a ≫ D)`;
with `Sigma.ι_desc` this peels off both `Sigma.desc`s, and the two braidings cancel by symmetry.
For the extension lemma: curry, use `Sigma.hom_ext` and naturality in the first variable; then
braid, curry again, and use `braiding_naturality_left` + `tensorHom_def'`.

Finite-coproduct bookkeeping for the total algebra `⊕ S_m`; used by
`GradedQCAlgebra.total_one_mul` / `total_mul_assoc` / `total_mul_comm` (`GradedAlgebraTotal.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `(a ▷ G) ≫ curry⁻¹ D = curry⁻¹ (a ≫ D)` (inverse form of `tensorObjHomEquiv_naturality_left`). -/
theorem whiskerRight_tensorObjHomEquiv_symm {F' F G H : X.Modules} (a : F' ⟶ F)
    (D : F ⟶ internalHom G H) :
    (a ▷ G) ≫ (tensorObjHomEquiv F G H).symm D = (tensorObjHomEquiv F' G H).symm (a ≫ D) := by
  apply (tensorObjHomEquiv F' G H).injective
  rw [Equiv.apply_symm_apply, ← tensorObjHomEquiv_naturality_left, Equiv.apply_symm_apply]

/-- Morphisms out of `(∐ F) ⊗ (∐ G)` are determined by their restrictions along `ι_i ⊗ₘ ι_j`. -/
theorem tensorObj_sigma_hom_ext {ι κ : Type w} (F : ι → X.Modules) (G : κ → X.Modules)
    [HasCoproduct F] [HasCoproduct G] {H : X.Modules} {f g : (∐ F) ⊗ (∐ G) ⟶ H}
    (h : ∀ i j, (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ f = (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ g) : f = g := by
  apply (tensorObjHomEquiv _ _ _).injective
  apply Sigma.hom_ext
  intro i
  rw [tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left]
  congr 1
  rw [← cancel_epi (β_ (∐ G) (F i)).hom]
  apply (tensorObjHomEquiv _ _ _).injective
  apply Sigma.hom_ext
  intro j
  rw [tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left]
  congr 1
  have key : ∀ k : (∐ F) ⊗ (∐ G) ⟶ H,
      (Sigma.ι G j ▷ F i) ≫ (β_ (∐ G) (F i)).hom ≫ (Sigma.ι F i ▷ ∐ G) ≫ k =
        (β_ (G j) (F i)).hom ≫ (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ k := by
    intro k
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
      ← Category.assoc (F i ◁ Sigma.ι G j), ← MonoidalCategory.tensorHom_def']
  rw [key, key, h]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem totalCurry_eq (F G H : X.Modules) :
    totalCurry F G H = AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv F G H := rfl

/-- `(ι_m ▷ C) ≫ totalMul S = totalMulRow S m`. -/
theorem whiskerRight_ι_totalMul (S : X.GradedQCAlgebra) (m : ℕ) :
    (Sigma.ι S.part m ▷ (∐ S.part)) ≫ totalMul S = totalMulRow S m := by
  unfold totalMul
  simp only [totalCurry_eq]
  rw [AlgebraicGeometry.Scheme.Modules.whiskerRight_tensorObjHomEquiv_symm, Sigma.ι_desc,
    Equiv.symm_apply_apply]

/-- `(S_m ◁ ι_n) ≫ totalMulRow S m = S.mul m n ≫ ι_{m+n}`. -/
theorem whiskerLeft_ι_totalMulRow (S : X.GradedQCAlgebra) (m n : ℕ) :
    (S.part m ◁ Sigma.ι S.part n) ≫ totalMulRow S m = S.mul m n ≫ Sigma.ι S.part (m + n) := by
  unfold totalMulRow
  simp only [totalCurry_eq]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right,
    Category.assoc, AlgebraicGeometry.Scheme.Modules.whiskerRight_tensorObjHomEquiv_symm,
    Sigma.ι_desc, Equiv.symm_apply_apply, SymmetricCategory.symmetry_assoc]

/-- **Component formula** for the multiplication of the total algebra. -/
@[reassoc]
theorem totalMul_component (S : X.GradedQCAlgebra) (m n : ℕ) :
    (Sigma.ι S.part m ⊗ₘ Sigma.ι S.part n) ≫ totalMul S = S.mul m n ≫ Sigma.ι S.part (m + n) := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc, whiskerRight_ι_totalMul,
    whiskerLeft_ι_totalMulRow]

/-- The same, phrased on `S.total`. -/
@[reassoc]
theorem total_mul_component (S : X.GradedQCAlgebra) (m n : ℕ) :
    (Sigma.ι S.part m ⊗ₘ Sigma.ι S.part n) ≫ S.total.mul = S.mul m n ≫ Sigma.ι S.part (m + n) :=
  totalMul_component S m n

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
