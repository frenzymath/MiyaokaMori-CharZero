import MiyaokaMori.Prelude

/-! # Tensor products of graded commutative monoids

The three axioms of a graded commutative monoid in a symmetric monoidal category (`IsGradedMonoid`, a
`Prop`), and the fact that **the tensor product of two graded monoids is a graded monoid** (indexed by
the product `ι₁ × ι₂`; multiplication = rearrange by `tensorμ`, then multiply factorwise; unit
`(λ_ 𝟙).inv ≫ (η₁ ⊗ η₂)`). This is the abstract content of each step of the induction on `r` for the
weighted symmetric tensor `weightedSymTensor r W = ⊗_{q<r} Sym^{d q}(W q)`.

Reference: standard (tensor product of monoid objects in a symmetric monoidal category; the graded
version of Mathlib's `Mon_.tensorObj`).

Proof:
* `one_mul`: `tensorμ_natural_left` moves `(η₁ ⊗ η₂) ▷ _` past `tensorμ`; use `one_mul` of each factor,
  then `tensor_left_unitality` (`λ_ (X₁ ⊗ X₂)` factors through `tensorμ 𝟙 𝟙`).
* `mul_assoc`: `tensorμ_natural_right` + `tensor_associativity` rewrite the left side as
  `(tensorμ ▷ _) ≫ tensorμ ≫ (assoc₁ ⊗ assoc₂)`; the right side uses `tensorμ_natural_left`.
* `mul_comm`: needs `β_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) ≫ tensorμ = tensorμ ≫ (β ⊗ β)` in a symmetric category
  (`braiding_tensorμ`; Mathlib has only the special case `SymmetricCategory.tensorμ_braid_swap` with
  `X₁ = X₂`, `Y₁ = Y₂`), then `mul_comm` of each factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace MiyaokaMori

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- `eqToHom ⊗ eqToHom = eqToHom` -/
theorem eqToHom_tensorHom {X X' Y Y' : C} (h : X = X') (h' : Y = Y') :
    eqToHom h ⊗ₘ eqToHom h' = eqToHom (show X ⊗ Y = X' ⊗ Y' by rw [h, h']) := by
  subst h; subst h'; simp

/-- The three axioms of a graded commutative monoid, for given data `part`, `mul`, `one` (index
rearrangements are propositional equalities transported by `eqToHom`). They correspond verbatim to the
three axioms of `AlgebraicGeometry.Scheme.GradedQCAlgebra` (with `ι = ℕ`). -/
structure IsGradedMonoid [BraidedCategory C] {ι : Type*} [AddCommMonoid ι]
    (part : ι → C) (mul : ∀ a b, part a ⊗ part b ⟶ part (a + b)) (one : 𝟙_ C ⟶ part 0) : Prop where
  one_mul : ∀ a, (one ▷ part a) ≫ mul 0 a =
    (λ_ (part a)).hom ≫ eqToHom (congrArg part (zero_add a).symm)
  mul_assoc : ∀ a b c, (α_ (part a) (part b) (part c)).hom ≫ (part a ◁ mul b c) ≫ mul a (b + c) =
    (mul a b ▷ part c) ≫ mul (a + b) c ≫ eqToHom (congrArg part (add_assoc a b c))
  mul_comm : ∀ a b, (β_ (part a) (part b)).hom ≫ mul b a =
    mul a b ≫ eqToHom (congrArg part (add_comm a b))

section Symmetric
variable [SymmetricCategory C]

/-- In a symmetric category the braiding is compatible with `tensorμ` (the general form of
`tensorμ_braid_swap`). -/
theorem braiding_tensorμ (X₁ X₂ Y₁ Y₂ : C) :
    (β_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)).hom ≫ tensorμ Y₁ Y₂ X₁ X₂ =
      tensorμ X₁ X₂ Y₁ Y₂ ≫ ((β_ X₁ Y₁).hom ⊗ₘ (β_ X₂ Y₂).hom) := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y₂ X₁, tensorHom_def]

/-- The trivial graded monoid: every piece is `𝟙_`, multiplication is the left unitor, the unit is
the identity. -/
theorem IsGradedMonoid.unit {ι : Type*} [AddCommMonoid ι] :
    IsGradedMonoid (fun _ : ι => 𝟙_ C) (fun _ _ => (λ_ (𝟙_ C)).hom) (𝟙 (𝟙_ C)) where
  one_mul _ := by simp
  mul_assoc _ _ _ := by simp; monoidal
  mul_comm _ _ := by simp; monoidal

/-- **The tensor product of two graded monoids**: indexed by `ι₁ × ι₂`, with `part (a, b) = P₁ a ⊗ P₂ b`. -/
theorem IsGradedMonoid.tensor {ι₁ ι₂ : Type*} [AddCommMonoid ι₁] [AddCommMonoid ι₂]
    {P₁ : ι₁ → C} {μ₁ : ∀ a b, P₁ a ⊗ P₁ b ⟶ P₁ (a + b)} {η₁ : 𝟙_ C ⟶ P₁ 0}
    {P₂ : ι₂ → C} {μ₂ : ∀ a b, P₂ a ⊗ P₂ b ⟶ P₂ (a + b)} {η₂ : 𝟙_ C ⟶ P₂ 0}
    (h₁ : IsGradedMonoid P₁ μ₁ η₁) (h₂ : IsGradedMonoid P₂ μ₂ η₂) :
    IsGradedMonoid (fun p : ι₁ × ι₂ => P₁ p.1 ⊗ P₂ p.2)
      (fun p q => tensorμ (P₁ p.1) (P₂ p.2) (P₁ q.1) (P₂ q.2) ≫ (μ₁ p.1 q.1 ⊗ₘ μ₂ p.2 q.2))
      ((λ_ (𝟙_ C)).inv ≫ (η₁ ⊗ₘ η₂)) where
  one_mul := by
    rintro ⟨a, b⟩
    dsimp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_add, Prod.snd_add]
    rw [comp_whiskerRight, Category.assoc, tensorμ_natural_left_assoc, tensorHom_comp_tensorHom,
      h₁.one_mul, h₂.one_mul, ← tensorHom_comp_tensorHom, ← tensor_left_unitality_assoc,
      eqToHom_tensorHom]
  mul_assoc := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    dsimp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_add, Prod.snd_add]
    rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom, ← tensor_associativity_assoc, tensorHom_comp_tensorHom,
      h₁.mul_assoc, h₂.mul_assoc, ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom,
      comp_whiskerRight]
    simp only [Category.assoc]
    rw [tensorμ_natural_left_assoc, eqToHom_tensorHom]
  mul_comm := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    dsimp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_add, Prod.snd_add]
    rw [← Category.assoc, braiding_tensorμ, Category.assoc, tensorHom_comp_tensorHom,
      h₁.mul_comm, h₂.mul_comm, ← tensorHom_comp_tensorHom, eqToHom_tensorHom, Category.assoc]

end Symmetric

section Cons
variable [SymmetricCategory C]

theorem tail_add' {r : ℕ} (f g : Fin (r + 1) → ℕ) : Fin.tail (f + g) = Fin.tail f + Fin.tail g := rfl
theorem tail_zero' {r : ℕ} : Fin.tail (0 : Fin (r + 1) → ℕ) = 0 := rfl

/-- The `Fin (r+1) → ℕ` version of `IsGradedMonoid.tensor` (index `d ↦ (d 0, Fin.tail d)`). Stated
separately so that the recursion of `weightedSymTensor` unfolds by definition, without index
arithmetic between `Prod` and `Pi` during unification (which is very expensive). The index arithmetic
is normalized in the proof with `dsimp only [Pi.add_apply, …]`. -/
theorem IsGradedMonoid.consTensor {r : ℕ}
    {P₁ : ℕ → C} {μ₁ : ∀ a b, P₁ a ⊗ P₁ b ⟶ P₁ (a + b)} {η₁ : 𝟙_ C ⟶ P₁ 0}
    {P₂ : (Fin r → ℕ) → C} {μ₂ : ∀ a b, P₂ a ⊗ P₂ b ⟶ P₂ (a + b)} {η₂ : 𝟙_ C ⟶ P₂ 0}
    (h₁ : IsGradedMonoid P₁ μ₁ η₁) (h₂ : IsGradedMonoid P₂ μ₂ η₂) :
    IsGradedMonoid (fun d : Fin (r + 1) → ℕ => P₁ (d 0) ⊗ P₂ (Fin.tail d))
      (fun d d' => tensorμ (P₁ (d 0)) (P₂ (Fin.tail d)) (P₁ (d' 0)) (P₂ (Fin.tail d')) ≫
        (μ₁ (d 0) (d' 0) ⊗ₘ μ₂ (Fin.tail d) (Fin.tail d')))
      ((λ_ (𝟙_ C)).inv ≫ (η₁ ⊗ₘ η₂)) where
  one_mul := by
    intro d
    dsimp only [Pi.add_apply, Pi.zero_apply, tail_add', tail_zero']
    rw [comp_whiskerRight, Category.assoc, tensorμ_natural_left_assoc, tensorHom_comp_tensorHom,
      h₁.one_mul, h₂.one_mul, ← tensorHom_comp_tensorHom, ← tensor_left_unitality_assoc,
      eqToHom_tensorHom]
  mul_assoc := by
    intro d d' d''
    dsimp only [Pi.add_apply, Pi.zero_apply, tail_add', tail_zero']
    rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom, ← tensor_associativity_assoc, tensorHom_comp_tensorHom,
      h₁.mul_assoc, h₂.mul_assoc, ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom,
      comp_whiskerRight]
    simp only [Category.assoc]
    rw [tensorμ_natural_left_assoc, eqToHom_tensorHom]
  mul_comm := by
    intro d d'
    dsimp only [Pi.add_apply, Pi.zero_apply, tail_add', tail_zero']
    rw [← Category.assoc, braiding_tensorμ, Category.assoc, tensorHom_comp_tensorHom,
      h₁.mul_comm, h₂.mul_comm, ← tensorHom_comp_tensorHom, eqToHom_tensorHom, Category.assoc]

end Cons

end MiyaokaMori
