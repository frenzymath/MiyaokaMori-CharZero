import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.GradedMonoidTensor

/-! # Graded-monoid axioms for tensor power families

Graded-monoid axioms for a "tensor power" family in a symmetric monoidal category.

Setting: `C` monoidal, `L : C`, a family `P : ℕ → C` together with comparison isomorphisms
`c e : P (e+1) ≅ P e ⊗ L`, an isomorphism `η : 𝟙_ C ≅ P 0`, and multiplication maps
`μ m n : P m ⊗ P n ⟶ P (m + n)` satisfying the two recursion equations (`IsTensorPowMul`)

* `μ m 0 = (P m ◁ η.inv) ≫ (ρ_ (P m)).hom`,
* `μ m (n+1) = (P m ◁ (c n).hom) ≫ (α_ _ _ _).inv ≫ (μ m n ▷ L) ≫ (c (m+n)).inv`.

These are exactly the equations satisfied by the inverse of
`AlgebraicGeometry.Scheme.Modules.tensorPowAddIso` (`LineBundleSectionRing`) with `P = tensorPow L`,
`c e = tensorIsoTensorObj (tensorPow L e) L`, `η = eqToIso rfl`.

Results (all pure monoidal coherence + naturality, by induction on the second index):

* `IsTensorPowMul.one_mul`, `IsTensorPowMul.mul_assoc` hold in any monoidal category;
* `IsTensorPowMul.mul_succ_left`: the "left" recursion `μ (n+1) m` is obtained from `μ n m` by
  passing `L` across `P m` with the braiding `β_ L (P m)` — this needs `C` symmetric and
  `(β_ L L).hom = 𝟙 _` (the symmetric group acts trivially on the powers of `L`; for a line
  bundle this is `Modules.braiding_hom_eq_id_of_isLineBundle`, Stacks 01CR);
* `IsTensorPowMul.mul_comm` (same hypotheses), and the bundle
  `IsTensorPowMul.isGradedMonoid : MiyaokaMori.IsGradedMonoid P μ η.hom`.

Index bookkeeping: the equations `0 + m = m`, `m + n + p = m + (n + p)`, `m + n = n + m` are
transported with `eqToHom (congrArg P _)`; the three transport lemmas `c_hom_eqToHom`,
`eqToHom_whiskerRight_c_inv`, `whiskerRight_eqToHom_mul` are proved by `subst`.

Source: standard (the tensor algebra `⊕ L^{⊗n}` is a graded monoid; commutativity for an
invertible object). No literature dependence beyond Mathlib's coherence lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace MiyaokaMori

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The recursion equations characterising the multiplication `μ` of the tensor-power graded
monoid: `μ m 0` is the right unitor (after identifying `P 0 ≅ 𝟙_`), and `μ m (n+1)` is
`μ m n ▷ L` conjugated by the comparison isomorphisms `c`. -/
structure IsTensorPowMul (L : C) (P : ℕ → C) (c : ∀ e, P (e + 1) ≅ P e ⊗ L) (η : 𝟙_ C ≅ P 0)
    (μ : ∀ m n, P m ⊗ P n ⟶ P (m + n)) : Prop where
  mul_zero : ∀ m, μ m 0 = (P m ◁ η.inv) ≫ (ρ_ (P m)).hom
  mul_succ : ∀ m n, μ m (n + 1) =
    (P m ◁ (c n).hom) ≫ (α_ (P m) (P n) L).inv ≫ (μ m n ▷ L) ≫ (c (m + n)).inv

section Transport

variable {L : C} {P : ℕ → C} (c : ∀ e, P (e + 1) ≅ P e ⊗ L)

/-- Transport of the comparison isomorphism along an index equality. -/
theorem c_hom_eqToHom {a b : ℕ} (h : a = b) :
    (c a).hom ≫ (eqToHom (congrArg P h) ▷ L) =
      eqToHom (congrArg P (congrArg (· + 1) h)) ≫ (c b).hom := by
  subst h; simp

@[reassoc]
theorem eqToHom_whiskerRight_c_inv {a b : ℕ} (h : a = b) :
    (eqToHom (congrArg P h) ▷ L) ≫ (c b).inv =
      (c a).inv ≫ eqToHom (congrArg P (congrArg (· + 1) h)) := by
  subst h; simp

variable (μ : ∀ m n, P m ⊗ P n ⟶ P (m + n))

theorem whiskerRight_eqToHom_mul {a b : ℕ} (h : a = b) (n : ℕ) :
    (eqToHom (congrArg P h) ▷ P n) ≫ μ b n =
      μ a n ≫ eqToHom (congrArg P (congrArg (· + n) h)) := by
  subst h; simp

theorem whiskerLeft_eqToHom_mul (m : ℕ) {a b : ℕ} (h : a = b) :
    (P m ◁ eqToHom (congrArg P h)) ≫ μ m b =
      μ m a ≫ eqToHom (congrArg P (congrArg (m + ·) h)) := by
  subst h; simp

end Transport

/-- A pentagon-type coherence identity used twice below (`monoidal`). -/
theorem assoc_coh (A B D E : C) :
    (α_ A B (D ⊗ E)).hom ≫ (A ◁ (α_ B D E).inv) ≫ (α_ A (B ⊗ D) E).inv =
      (α_ (A ⊗ B) D E).inv ≫ ((α_ A B D).hom ▷ E) := by
  monoidal

namespace IsTensorPowMul

variable {L : C} {P : ℕ → C} {c : ∀ e, P (e + 1) ≅ P e ⊗ L} {η : 𝟙_ C ≅ P 0}
  {μ : ∀ m n, P m ⊗ P n ⟶ P (m + n)} (h : IsTensorPowMul L P c η μ)
include h

/-- Unit law (`IsGradedMonoid.one_mul`), by induction on `m`. -/
theorem one_mul (m : ℕ) :
    (η.hom ▷ P m) ≫ μ 0 m = (λ_ (P m)).hom ≫ eqToHom (congrArg P (zero_add m).symm) := by
  induction m with
  | zero =>
    rw [h.mul_zero, ← whisker_exchange_assoc, rightUnitor_naturality, ← unitors_equal,
      leftUnitor_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Category.comp_id _).symm
  | succ m ih =>
    rw [h.mul_succ, ← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, ih, comp_whiskerRight, Category.assoc,
      eqToHom_whiskerRight_c_inv c (zero_add m).symm, ← leftUnitor_tensor_hom_assoc,
      leftUnitor_naturality_assoc, Iso.hom_inv_id_assoc]

/-- Associativity (`IsGradedMonoid.mul_assoc`), by induction on `p`. -/
theorem mul_assoc (m n p : ℕ) :
    (α_ (P m) (P n) (P p)).hom ≫ (P m ◁ μ n p) ≫ μ m (n + p) =
      (μ m n ▷ P p) ≫ μ (m + n) p ≫ eqToHom (congrArg P (add_assoc m n p)) := by
  induction p with
  | zero =>
    dsimp only [Nat.add_zero]
    rw [h.mul_zero, h.mul_zero, eqToHom_refl, Category.comp_id, whiskerLeft_comp, Category.assoc,
      ← associator_naturality_right_assoc, ← rightUnitor_tensor_hom_assoc, ← rightUnitor_naturality,
      whisker_exchange_assoc]
  | succ p ih =>
    have e1 : μ m (n + (p + 1)) = _ := h.mul_succ m (n + p)
    rw [h.mul_succ, e1, h.mul_succ]
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_inv_hom_assoc]
    rw [associator_inv_naturality_middle_assoc, ← associator_naturality_right_assoc]
    rw [reassoc_of% assoc_coh, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      Category.assoc (α_ _ _ _).hom, ih,
      comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
      eqToHom_whiskerRight_c_inv c (add_assoc m n p), ← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc]

section Symmetric

variable [SymmetricCategory C] (hβ : (β_ L L).hom = 𝟙 (L ⊗ L))
include hβ

/-- The "left" recursion: `μ (n+1) m` in terms of `μ n m`, passing `L` across `P m` with the
braiding. Induction on `m`; the step uses `(β_ L L).hom = 𝟙`. -/
theorem mul_succ_left (n m : ℕ) :
    μ (n + 1) m =
      ((c n).hom ▷ P m) ≫ (α_ (P n) L (P m)).hom ≫ (P n ◁ (β_ L (P m)).hom) ≫
        (α_ (P n) (P m) L).inv ≫ (μ n m ▷ L) ≫ (c (n + m)).inv ≫
        eqToHom (congrArg P (Nat.add_right_comm n m 1)) := by
  induction m with
  | zero =>
    dsimp only [Nat.add_zero]
    rw [h.mul_zero, h.mul_zero, eqToHom_refl, Category.comp_id]
    have hb : (β_ L (P 0)).hom = (L ◁ η.inv) ≫ (β_ L (𝟙_ C)).hom ≫ (η.hom ▷ L) := by
      rw [BraidedCategory.braiding_naturality_right_assoc, inv_hom_whiskerRight, Category.comp_id]
    rw [hb, braiding_tensorUnit_right]
    simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, whiskerLeft_hom_inv,
      id_whiskerRight, Category.id_comp, triangle_assoc_comp_right_assoc, whiskerLeft_inv_hom_assoc,
      ← associator_naturality_right_assoc, ← rightUnitor_tensor_hom_assoc, ← whisker_exchange_assoc,
      rightUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  | succ m ih =>
    have hb : (β_ L (P (m + 1))).hom =
        (L ◁ (c m).hom) ≫ (β_ L (P m ⊗ L)).hom ≫ ((c m).inv ▷ L) := by
      rw [BraidedCategory.braiding_naturality_right_assoc, hom_inv_whiskerRight, Category.comp_id]
    rw [h.mul_succ, ih, hb, BraidedCategory.braiding_tensor_right_hom, hβ, whiskerLeft_id, Category.id_comp,
      h.mul_succ n m]
    simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
    rw [eqToHom_whiskerRight_c_inv c (Nat.add_right_comm n m 1),
      ← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
      ← associator_naturality_right_assoc, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc (P n ◁ (c m).inv), whiskerLeft_inv_hom, id_whiskerRight,
      Category.id_comp, associator_inv_naturality_middle_assoc, reassoc_of% assoc_coh]
    rfl

/-- Commutativity (`IsGradedMonoid.mul_comm`), by induction on `n`. -/
theorem mul_comm (m n : ℕ) :
    (β_ (P m) (P n)).hom ≫ μ n m = μ m n ≫ eqToHom (congrArg P (add_comm m n)) := by
  induction n with
  | zero =>
    dsimp only [Nat.add_zero]
    have hb : (β_ (P m) (P 0)).hom = (P m ◁ η.inv) ≫ (β_ (P m) (𝟙_ C)).hom ≫ (η.hom ▷ P m) := by
      rw [BraidedCategory.braiding_naturality_right_assoc, inv_hom_whiskerRight, Category.comp_id]
    rw [hb, braiding_tensorUnit_right, h.mul_zero]
    simp only [Category.assoc]
    rw [h.one_mul, Iso.inv_hom_id_assoc]
  | succ n ih =>
    rw [h.mul_succ_left hβ, ← BraidedCategory.braiding_naturality_right_assoc,
      BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp,
      Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, ih, comp_whiskerRight, Category.assoc,
      eqToHom_whiskerRight_c_inv_assoc c (add_comm m n), h.mul_succ]
    simp only [Category.assoc, eqToHom_trans]

/-- The tensor-power family is a graded commutative monoid. -/
theorem isGradedMonoid : IsGradedMonoid P μ η.hom where
  one_mul := h.one_mul
  mul_assoc := h.mul_assoc
  mul_comm := h.mul_comm hβ

end Symmetric

end IsTensorPowMul

end MiyaokaMori
