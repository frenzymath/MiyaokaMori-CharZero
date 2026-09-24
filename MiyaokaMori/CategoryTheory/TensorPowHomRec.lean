import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowGradedMonoid
import MiyaokaMori.CategoryTheory.TensorPairMul

/-! # A recursively defined family out of tensor powers is multiplicative

Setting (`C` monoidal): a tensor-power family `P : ℕ → C` of an object `A` with comparison isomorphisms
`c e : P (e+1) ≅ P e ⊗ A`, `η : 𝟙_ ≅ P 0`, and splitting isomorphisms `s m n : P (m+n) ≅ P m ⊗ P n` whose
inverses satisfy the two recursion equations `IsTensorPowMul` (`TensorPowGradedMonoid`;
for `P = tensorPow A`, `s = tensorPowAddIso A` these hold by definition).

A target family `T : ℕ → C` with a "step multiplication" `σ e : T e ⊗ A ⟶ T (e+1)`, a unit `θ : 𝟙_ ⟶ T 0`
and block multiplications `ν m n : T m ⊗ T n ⟶ T (m+n)`, and a family `Ψ e : P e ⟶ T e` defined by the
recursion `Ψ 0 = η.inv ≫ θ`, `Ψ (e+1) = (c e).hom ≫ (Ψ e ▷ A) ≫ σ e` (`IsTensorPowHomRec`).

**Theorem** (`IsTensorPowHomRec.add`): if `ν` satisfies the right unit law `(T m ◁ θ) ≫ ν m 0 = ρ_` and
the associativity step `(T m ◁ σ n) ≫ ν m (n+1) = α⁻¹ ≫ (ν m n ▷ A) ≫ σ (m+n)`, then
`Ψ (m+n) = (s m n).hom ≫ (Ψ m ⊗ Ψ n) ≫ ν m n` for all `m n` (induction on `n`).

**Product form** (`IsTensorPowHomRec.add_of_combMul`, `C` braided): when `T e = t (O e) (G e)` is a product of two
families and `σ`, `ν`, `θ` are the pair products (`MiyaokaMori.combMul`, `TensorPairMul.lean`) of componentwise
step/block multiplications and units, the componentwise right unit laws and associativity steps suffice. The concrete
instantiation then only has to supply componentwise laws (small statements), which keeps the elaboration of the
concrete instance cheap.

This is the abstract content of the block multiplicativity of `twistPullbackPow`: there `A = O(q) ⊗ π^*Q`,
`T e = O(qe) ⊗ π^*Q^{⊗e}`, `σ e` and `ν m n` are built from `twistMul` and `pullbackTensorIso⁻¹`.

Source: standard (the free graded monoid on one generator; a multiplicative map out of it is determined by
its value on the generator). Pure monoidal coherence.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace MiyaokaMori

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The recursion defining a family `Ψ e : P e ⟶ T e` out of a tensor-power family:
`Ψ 0 = η.inv ≫ θ` and `Ψ (e+1) = (c e).hom ≫ (Ψ e ▷ A) ≫ σ e`. -/
structure IsTensorPowHomRec (A : C) (P : ℕ → C) (c : ∀ e, P (e + 1) ≅ P e ⊗ A) (η : 𝟙_ C ≅ P 0)
    (T : ℕ → C) (σ : ∀ e, T e ⊗ A ⟶ T (e + 1)) (θ : 𝟙_ C ⟶ T 0) (Ψ : ∀ e, P e ⟶ T e) : Prop where
  zero : Ψ 0 = η.inv ≫ θ
  succ : ∀ e, Ψ (e + 1) = (c e).hom ≫ (Ψ e ▷ A) ≫ σ e

namespace IsTensorPowHomRec

variable {A : C} {P : ℕ → C} {c : ∀ e, P (e + 1) ≅ P e ⊗ A} {η : 𝟙_ C ≅ P 0}
  {s : ∀ m n, P (m + n) ≅ P m ⊗ P n}
  {T : ℕ → C} {σ : ∀ e, T e ⊗ A ⟶ T (e + 1)} {θ : 𝟙_ C ⟶ T 0} {Ψ : ∀ e, P e ⟶ T e}

/-- `(s m 0).hom = (ρ_ (P m)).inv ≫ (P m ◁ η.hom)` (inverse of `IsTensorPowMul.mul_zero`). -/
theorem s_zero_hom (hs : IsTensorPowMul A P c η (fun m n => (s m n).inv)) (m : ℕ) :
    (s m 0).hom = (ρ_ (P m)).inv ≫ (P m ◁ η.hom) := by
  symm
  rw [← Category.comp_id (s m 0).hom, ← Iso.inv_comp_eq, hs.mul_zero m]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, whiskerLeft_inv_hom]

/-- `(s m (n+1)).hom ≫ (P m ◁ (c n).hom) ≫ (α_ _ _ _).inv = (c (m+n)).hom ≫ ((s m n).hom ▷ A)`
(inverse of `IsTensorPowMul.mul_succ`). -/
theorem s_succ_hom (hs : IsTensorPowMul A P c η (fun m n => (s m n).inv)) (m n : ℕ) :
    (s m (n + 1)).hom ≫ (P m ◁ (c n).hom) ≫ (α_ (P m) (P n) A).inv =
      (c (m + n)).hom ≫ ((s m n).hom ▷ A) := by
  have h := hs.mul_succ m n
  rw [← Iso.eq_inv_comp, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, inv_hom_whiskerRight, Category.comp_id]

variable (hs : IsTensorPowMul A P c η (fun m n => (s m n).inv)) (hΨ : IsTensorPowHomRec A P c η T σ θ Ψ)
  (ν : ∀ m n, T m ⊗ T n ⟶ T (m + n))
  (hunit : ∀ m, (T m ◁ θ) ≫ ν m 0 = (ρ_ (T m)).hom)
  (hassoc : ∀ m n, (T m ◁ σ n) ≫ ν m (n + 1) = (α_ (T m) (T n) A).inv ≫ (ν m n ▷ A) ≫ σ (m + n))
include hs hΨ hunit hassoc

/-- **Block multiplicativity of a recursively defined family.** -/
theorem add (m n : ℕ) : Ψ (m + n) = (s m n).hom ≫ (Ψ m ⊗ₘ Ψ n) ≫ ν m n := by
  induction n with
  | zero =>
    show Ψ m = _
    rw [s_zero_hom hs, hΨ.zero, tensorHom_def', whiskerLeft_comp]
    simp only [Category.assoc]
    rw [whiskerLeft_hom_inv_assoc, whisker_exchange_assoc, hunit]
    rw [whiskerRight_id]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  | succ n ih =>
    show Ψ (m + n + 1) = _
    rw [hΨ.succ (m + n), hΨ.succ n, tensorHom_def' (Ψ m), whiskerLeft_comp, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc, hassoc, associator_inv_naturality_left_assoc,
      associator_inv_naturality_middle_assoc, reassoc_of% (s_succ_hom hs m n),
      ← comp_whiskerRight_assoc (P m ◁ Ψ n) (Ψ m ▷ T n), ← tensorHom_def',
      ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
    simp only [Category.assoc]
    rw [← ih]

end IsTensorPowHomRec

section Product

variable [BraidedCategory C] {t : C → C → C} (τ : ∀ X Y : C, t X Y ≅ X ⊗ Y)

/-- **Block multiplicativity, product form.** `T e := t (O e) (G e)`, `A := t O₁ G₁`,
`σ e := combMul τ (κ₁ e) (κ₂ e)`, `ν m n := combMul τ (μ₁ m n) (μ₂ m n)`, `θ := (λ_ 𝟙_).inv ≫ (u ⊗ ε) ≫ τ⁻¹`;
the hypotheses are the componentwise right unit laws `hu₁ hu₂` and associativity steps `ha₁ ha₂`. -/
theorem IsTensorPowHomRec.add_of_combMul {O G : ℕ → C} {O₁ G₁ : C}
    (κ₁ : ∀ e, O e ⊗ O₁ ⟶ O (e + 1)) (κ₂ : ∀ e, G e ⊗ G₁ ⟶ G (e + 1))
    (μ₁ : ∀ m n, O m ⊗ O n ⟶ O (m + n)) (μ₂ : ∀ m n, G m ⊗ G n ⟶ G (m + n))
    (u : 𝟙_ C ⟶ O 0) (ε : 𝟙_ C ⟶ G 0)
    (hu₁ : ∀ m, (O m ◁ u) ≫ μ₁ m 0 = (ρ_ (O m)).hom) (hu₂ : ∀ m, (G m ◁ ε) ≫ μ₂ m 0 = (ρ_ (G m)).hom)
    (ha₁ : ∀ m n, (O m ◁ κ₁ n) ≫ μ₁ m (n + 1) = (α_ (O m) (O n) O₁).inv ≫ (μ₁ m n ▷ O₁) ≫ κ₁ (m + n))
    (ha₂ : ∀ m n, (G m ◁ κ₂ n) ≫ μ₂ m (n + 1) = (α_ (G m) (G n) G₁).inv ≫ (μ₂ m n ▷ G₁) ≫ κ₂ (m + n))
    {P : ℕ → C} {c : ∀ e, P (e + 1) ≅ P e ⊗ t O₁ G₁} {η : 𝟙_ C ≅ P 0} {s : ∀ m n, P (m + n) ≅ P m ⊗ P n}
    (hs : IsTensorPowMul (t O₁ G₁) P c η (fun m n => (s m n).inv))
    {Ψ : ∀ e, P e ⟶ t (O e) (G e)}
    (hΨ : IsTensorPowHomRec (t O₁ G₁) P c η (fun e => t (O e) (G e)) (fun e => combMul τ (κ₁ e) (κ₂ e))
      ((λ_ (𝟙_ C)).inv ≫ (u ⊗ₘ ε) ≫ (τ (O 0) (G 0)).inv) Ψ)
    (m n : ℕ) :
    Ψ (m + n) = (s m n).hom ≫ (Ψ m ⊗ₘ Ψ n) ≫ combMul τ (μ₁ m n) (μ₂ m n) :=
  hΨ.add hs (fun m n => combMul τ (μ₁ m n) (μ₂ m n))
    (fun m => combMul_unit_right τ u ε (μ₁ m 0) (μ₂ m 0) (hu₁ m) (hu₂ m))
    (fun m n => combMul_assoc_step τ (κ₁ n) (μ₁ m (n + 1)) (μ₁ m n) (κ₁ (m + n)) (κ₂ n) (μ₂ m (n + 1)) (μ₂ m n)
      (κ₂ (m + n)) (ha₁ m n) (ha₂ m n)) m n

end Product


end MiyaokaMori
