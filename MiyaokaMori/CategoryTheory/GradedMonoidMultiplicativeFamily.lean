import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.GradedMonoidTensor

/-! # Multiplicative families into a commutative graded monoid

Setting: `C` a symmetric monoidal category, `(Q, ν, θ)` a commutative graded monoid indexed by an additive commutative
monoid `κ` (`MiyaokaMori.IsGradedMonoid`, `GradedMonoidTensor.lean`; for a `GradedQCAlgebra T` this is
`T.isGradedMonoid`).

* `gmul Q ν h : Q a ⊗ Q b ⟶ Q c` for `h : a + b = c` is the multiplication with a **flexible target index**
  (`ν a b ≫ eqToHom`). All index bookkeeping (`eqToHom` between `Q m` and `Q m'`) is absorbed into the proof argument,
  which is irrelevant, so the laws `gmul_assoc`, `gmul_comm`, `gmul_one_mul`, `gmul_mul_one` hold for *any* consistent
  indices and can be used by `rw` without transporting. (Because of proof irrelevance, `rw` does not instantiate
  Prop-valued arguments by unification: always pass the index proofs explicitly.)
* `IsGradedMonoid.gmul_interchange`: the middle-four interchange `(a·c)·(b·d) = (a·b)·(c·d)` along `tensorμ`, i.e. the
  multiplication of a commutative graded monoid is multiplicative. Proof: `tensorμ` unfolded, associativity three times
  and commutativity once (Bourbaki, Algebra III §4 no. 1: the multiplication of a commutative algebra is an algebra
  homomorphism).
* `IsGradedMonoidHom P μ η Q ν θ w hw hw0 Ψ` (Prop): a family `Ψ a : P a ⟶ Q (w a)` along an additive weight
  `w : ι → κ` is multiplicative and unital.
  - `IsGradedMonoidHom.unit`: the unit graded monoid maps into `Q` by `θ`;
  - `IsGradedMonoidHom.consTensor`: the tensor product of two multiplicative families is multiplicative for the
    `Fin (r+1) → ℕ` tensor graded monoid `IsGradedMonoid.consTensor` (this is where `gmul_interchange` is used);
  - `IsGradedMonoidHom.reindex`: change the weight function along a pointwise equality;
  - `IsGradedMonoidHom.transport`: change the source along an equality of graded monoids (used for the `dite` in
    `symGradedAlgebra`).

Reference: Bourbaki, Algebra III §4 no. 1 (tensor product of algebra homomorphisms into a commutative algebra) and §6 no. 1
Prop. 2 (universal property of `Sym`). Pure coherence. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace MiyaokaMori

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Gmul

variable {κ : Type*} [AddCommMonoid κ] (Q : κ → C) (ν : ∀ a b, Q a ⊗ Q b ⟶ Q (a + b))

/-- Multiplication with a flexible target index: `ν a b ≫ eqToHom`. -/
def gmul {a b c : κ} (h : a + b = c) : Q a ⊗ Q b ⟶ Q c :=
  ν a b ≫ eqToHom (congrArg Q h)

theorem gmul_rfl (a b : κ) : gmul Q ν (rfl : a + b = a + b) = ν a b := by
  simp [gmul]

theorem gmul_comp_eqToHom {a b c c' : κ} (h : a + b = c) (h' : c = c') :
    gmul Q ν h ≫ eqToHom (congrArg Q h') = gmul Q ν (h.trans h') := by
  simp [gmul]

theorem eqToHom_tensorHom_comp_gmul {a a' b b' c : κ} (ha : a = a') (hb : b = b') (h : a' + b' = c) :
    (eqToHom (congrArg Q ha) ⊗ₘ eqToHom (congrArg Q hb)) ≫ gmul Q ν h =
      gmul Q ν (by rw [ha, hb]; exact h) := by
  subst ha; subst hb; simp

theorem eqToHom_whiskerRight_comp_gmul {a a' b c : κ} (ha : a = a') (h : a' + b = c) :
    (eqToHom (congrArg Q ha) ▷ Q b) ≫ gmul Q ν h = gmul Q ν (by rw [ha]; exact h) := by
  subst ha; simp

theorem whiskerLeft_eqToHom_comp_gmul {a b b' c : κ} (hb : b = b') (h : a + b' = c) :
    (Q a ◁ eqToHom (congrArg Q hb)) ≫ gmul Q ν h = gmul Q ν (by rw [hb]; exact h) := by
  subst hb; simp

end Gmul

namespace IsGradedMonoid

section Braided

variable [BraidedCategory C] {κ : Type*} [AddCommMonoid κ] {Q : κ → C} {ν : ∀ a b, Q a ⊗ Q b ⟶ Q (a + b)}
  {θ : 𝟙_ C ⟶ Q 0} (hQ : IsGradedMonoid Q ν θ)
include hQ

theorem gmul_assoc {a b c bc ab m : κ} (h1 : b + c = bc) (h2 : a + bc = m) (h3 : a + b = ab)
    (h4 : ab + c = m) :
    (α_ (Q a) (Q b) (Q c)).hom ≫ (Q a ◁ gmul Q ν h1) ≫ gmul Q ν h2 =
      (gmul Q ν h3 ▷ Q c) ≫ gmul Q ν h4 := by
  subst h1; subst h3; subst h2
  simp only [gmul, eqToHom_refl, Category.comp_id]
  exact hQ.mul_assoc a b c

theorem gmul_comm {a b c : κ} (h : b + a = c) (h' : a + b = c) :
    (β_ (Q a) (Q b)).hom ≫ gmul Q ν h = gmul Q ν h' := by
  subst h
  simp only [gmul, eqToHom_refl, Category.comp_id]
  exact hQ.mul_comm a b

theorem gmul_one_mul {a c : κ} (h : 0 + a = c) (h' : a = c) :
    (θ ▷ Q a) ≫ gmul Q ν h = (λ_ (Q a)).hom ≫ eqToHom (congrArg Q h') := by
  subst h'
  simp only [gmul, eqToHom_refl, Category.comp_id, ← Category.assoc, hQ.one_mul]
  simp

theorem gmul_mul_one {a c : κ} (h : a + 0 = c) (h' : a = c) :
    (Q a ◁ θ) ≫ gmul Q ν h = (ρ_ (Q a)).hom ≫ eqToHom (congrArg Q h') := by
  rw [← hQ.gmul_comm (by rw [add_comm]; exact h) h, ← Category.assoc,
    BraidedCategory.braiding_naturality_right, Category.assoc, hQ.gmul_one_mul _ h',
    ← Category.assoc, braiding_leftUnitor]

/-- `(θ ⊗ θ) ≫ ν = (λ_ 𝟙).hom ≫ θ` (with flexible indices). -/
theorem tensorHom_one_one_comp_gmul {c : κ} (h : 0 + 0 = c) (h' : 0 = c) :
    (θ ⊗ₘ θ) ≫ gmul Q ν h = (λ_ (𝟙_ C)).hom ≫ θ ≫ eqToHom (congrArg Q h') := by
  rw [tensorHom_def, Category.assoc, hQ.gmul_mul_one h h', ← Category.assoc,
    rightUnitor_naturality, unitors_equal, Category.assoc]

end Braided

section Symmetric

variable [SymmetricCategory C] {κ : Type*} [AddCommMonoid κ] {Q : κ → C}
  {ν : ∀ a b, Q a ⊗ Q b ⟶ Q (a + b)} {θ : 𝟙_ C ⟶ Q 0} (hQ : IsGradedMonoid Q ν θ)
include hQ

/-- **Middle-four interchange** in a commutative graded monoid: `(a·c)·(b·d) = (a·b)·(c·d)` along `tensorμ`. -/
theorem gmul_interchange {a b c d ac bd ab cd m : κ}
    (h1 : a + c = ac) (h2 : b + d = bd) (h3 : ac + bd = m) (h4 : a + b = ab) (h5 : c + d = cd)
    (h6 : ab + cd = m) :
    tensorμ (Q a) (Q b) (Q c) (Q d) ≫ (gmul Q ν h1 ⊗ₘ gmul Q ν h2) ≫ gmul Q ν h3 =
      (gmul Q ν h4 ⊗ₘ gmul Q ν h5) ≫ gmul Q ν h6 := by
  have hcd : c + d = cd := h5
  have hbd : b + d = bd := h2
  have hbcd : b + cd = b + cd := rfl
  have hcbd : c + bd = b + cd := by rw [← hbd, ← hcd, add_left_comm]
  have hm : a + (b + cd) = m := by rw [← h6, ← h4, ← h5, add_assoc]
  have hcb : c + b = c + b := rfl
  have hbc : b + c = c + b := add_comm b c
  have hcbd' : c + b + d = b + cd := by rw [add_assoc, hbd, hcbd]
  -- right-hand side: `(a·b)·(c·d) = a·(b·(c·d))`
  have hR : (gmul Q ν h4 ⊗ₘ gmul Q ν h5) ≫ gmul Q ν h6 =
      (α_ (Q a) (Q b) (Q c ⊗ Q d)).hom ≫ (Q a ◁ (Q b ◁ gmul Q ν hcd)) ≫
        (Q a ◁ gmul Q ν hbcd) ≫ gmul Q ν hm := by
    rw [tensorHom_def', Category.assoc, ← hQ.gmul_assoc hbcd hm h4 h6, ← Category.assoc,
      associator_naturality_right, Category.assoc]
  -- left-hand side: `(a·c)·(b·d) = a·(c·(b·d))`
  have hL : (gmul Q ν h1 ⊗ₘ gmul Q ν h2) ≫ gmul Q ν h3 =
      ((Q a ⊗ Q c) ◁ gmul Q ν hbd) ≫ (α_ (Q a) (Q c) (Q bd)).hom ≫ (Q a ◁ gmul Q ν hcbd) ≫
        gmul Q ν hm := by
    rw [tensorHom_def', Category.assoc, ← hQ.gmul_assoc hcbd hm h1 h3]
  -- the inner rearrangement `c·(b·d) = b·(c·d)` after the braiding
  have hinner : (α_ (Q b) (Q c) (Q d)).inv ≫ ((β_ (Q b) (Q c)).hom ▷ Q d) ≫
      (α_ (Q c) (Q b) (Q d)).hom ≫ (Q c ◁ gmul Q ν hbd) ≫ gmul Q ν hcbd =
        (Q b ◁ gmul Q ν hcd) ≫ gmul Q ν hbcd := by
    rw [hQ.gmul_assoc hbd hcbd hcb hcbd', ← comp_whiskerRight_assoc, hQ.gmul_comm hcb hbc,
      ← hQ.gmul_assoc hcd hbcd hbc hcbd', Iso.inv_hom_id_assoc]
  rw [hL, hR]
  simp only [tensorμ, Category.assoc]
  rw [associator_naturality_right_assoc, Iso.inv_hom_id_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [← hinner]

/-- Re-association of a triple product `((k₁·k₂)·k₃) = k₁·(k₂·k₃)` of maps into `Q`. -/
theorem tensorHom_gmul_tensorHom_comp_gmul {a b c ab bc m : κ} {A B D : C} (k₁ : A ⟶ Q a) (k₂ : B ⟶ Q b)
    (k₃ : D ⟶ Q c) (h₁ : a + b = ab) (h₂ : ab + c = m) (h₃ : b + c = bc) (h₄ : a + bc = m) :
    (((k₁ ⊗ₘ k₂) ≫ gmul Q ν h₁) ⊗ₘ k₃) ≫ gmul Q ν h₂ =
      (α_ A B D).hom ≫ (k₁ ⊗ₘ ((k₂ ⊗ₘ k₃) ≫ gmul Q ν h₃)) ≫ gmul Q ν h₄ := by
  have e : ((k₁ ⊗ₘ k₂) ≫ gmul Q ν h₁) ⊗ₘ k₃ = ((k₁ ⊗ₘ k₂) ⊗ₘ k₃) ≫ (gmul Q ν h₁ ▷ Q c) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have e' : (k₁ ⊗ₘ (k₂ ⊗ₘ k₃)) ≫ (Q a ◁ gmul Q ν h₃) = k₁ ⊗ₘ ((k₂ ⊗ₘ k₃) ≫ gmul Q ν h₃) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [e, Category.assoc, ← hQ.gmul_assoc h₃ h₄ h₁ h₂, associator_naturality_assoc, ← e', Category.assoc]

/-- Swapping the last two factors of a product `(k·g)·g` of maps into `Q` does not change it. -/
theorem braiding_last_two_comp_gmul {a n an m : κ} {A B : C} (k : A ⟶ Q a) (g : B ⟶ Q n)
    (h₁ : a + n = an) (h₂ : an + n = m) :
    (α_ A B B).hom ≫ (A ◁ (β_ B B).hom) ≫ (α_ A B B).inv ≫
        (((k ⊗ₘ g) ≫ gmul Q ν h₁) ⊗ₘ g) ≫ gmul Q ν h₂ =
      (((k ⊗ₘ g) ≫ gmul Q ν h₁) ⊗ₘ g) ≫ gmul Q ν h₂ := by
  have h₄ : a + (n + n) = m := by rw [← add_assoc, h₁, h₂]
  rw [hQ.tensorHom_gmul_tensorHom_comp_gmul k g g h₁ h₂ rfl h₄, Iso.inv_hom_id_assoc, ← id_tensorHom,
    ← Category.assoc (𝟙 A ⊗ₘ (β_ B B).hom), tensorHom_comp_tensorHom, Category.id_comp,
    ← Category.assoc (β_ B B).hom, ← BraidedCategory.braiding_naturality, Category.assoc,
    hQ.gmul_comm rfl rfl]

end Symmetric

end IsGradedMonoid

section Hom

variable {ι κ : Type*} [AddCommMonoid ι] [AddCommMonoid κ]

/-- A family `Ψ a : P a ⟶ Q (w a)` along an additive weight `w` is a **graded monoid homomorphism**:
multiplicative (with flexible target index `gmul`) and unital. -/
structure IsGradedMonoidHom (P : ι → C) (μ : ∀ a b, P a ⊗ P b ⟶ P (a + b)) (η : 𝟙_ C ⟶ P 0)
    (Q : κ → C) (ν : ∀ a b, Q a ⊗ Q b ⟶ Q (a + b)) (θ : 𝟙_ C ⟶ Q 0)
    (w : ι → κ) (hw : ∀ a b, w (a + b) = w a + w b) (hw0 : w 0 = 0)
    (Ψ : ∀ a, P a ⟶ Q (w a)) : Prop where
  map_mul : ∀ a b, μ a b ≫ Ψ (a + b) = (Ψ a ⊗ₘ Ψ b) ≫ gmul Q ν (hw a b).symm
  map_one : η ≫ Ψ 0 = θ ≫ eqToHom (congrArg Q hw0.symm)

namespace IsGradedMonoidHom

variable {P : ι → C} {μ : ∀ a b, P a ⊗ P b ⟶ P (a + b)} {η : 𝟙_ C ⟶ P 0}
  {Q : κ → C} {ν : ∀ a b, Q a ⊗ Q b ⟶ Q (a + b)} {θ : 𝟙_ C ⟶ Q 0}

/-- Change the weight function along a pointwise equality. -/
theorem reindex {w : ι → κ} {hw : ∀ a b, w (a + b) = w a + w b} {hw0 : w 0 = 0} {Ψ : ∀ a, P a ⟶ Q (w a)}
    (h : IsGradedMonoidHom P μ η Q ν θ w hw hw0 Ψ) (w' : ι → κ) (hww' : ∀ a, w a = w' a)
    (hw' : ∀ a b, w' (a + b) = w' a + w' b) (hw0' : w' 0 = 0) :
    IsGradedMonoidHom P μ η Q ν θ w' hw' hw0' (fun a => Ψ a ≫ eqToHom (congrArg Q (hww' a))) where
  map_mul a b := by
    rw [← Category.assoc, h.map_mul, Category.assoc, gmul_comp_eqToHom Q ν (hw a b).symm (hww' (a + b)),
      ← tensorHom_comp_tensorHom, Category.assoc, eqToHom_tensorHom_comp_gmul Q ν (hww' a) (hww' b)]
  map_one := by
    rw [← Category.assoc, h.map_one, Category.assoc, eqToHom_trans]

/-- Change the source along an equality of the source data (used for the `dite` in `symGradedAlgebra`). -/
theorem transport {P' : ι → C} {μ' : ∀ a b, P' a ⊗ P' b ⟶ P' (a + b)} {η' : 𝟙_ C ⟶ P' 0}
    (hP : P = P') (hμ : HEq μ μ') (hη : HEq η η')
    {w : ι → κ} {hw : ∀ a b, w (a + b) = w a + w b} {hw0 : w 0 = 0} {Ψ' : ∀ a, P' a ⟶ Q (w a)}
    (h : IsGradedMonoidHom P' μ' η' Q ν θ w hw hw0 Ψ') :
    IsGradedMonoidHom P μ η Q ν θ w hw hw0 (fun a => eqToHom (congrArg (fun P => P a) hP) ≫ Ψ' a) := by
  subst hP
  cases hμ; cases hη
  simpa using h

/-- The unit graded monoid (every piece `𝟙_`, `GradedMonoidTensor.IsGradedMonoid.unit`) maps into `Q` by `θ`. -/
theorem unit [BraidedCategory C] (hQ : IsGradedMonoid Q ν θ) :
    IsGradedMonoidHom (fun _ : ι => 𝟙_ C) (fun _ _ => (λ_ (𝟙_ C)).hom) (𝟙 (𝟙_ C)) Q ν θ
      (fun _ => 0) (fun _ _ => (zero_add 0).symm) rfl (fun _ => θ) where
  map_mul _ _ := by
    rw [hQ.tensorHom_one_one_comp_gmul (zero_add (0 : κ)) rfl, eqToHom_refl, Category.comp_id]
  map_one := by simp

/-- **Tensor product of two multiplicative families** into a commutative graded monoid, for the
`Fin (r+1) → ℕ` tensor graded monoid `IsGradedMonoid.consTensor`. -/
theorem consTensor [SymmetricCategory C] {r : ℕ} (hQ : IsGradedMonoid Q ν θ)
    {P₁ : ℕ → C} {μ₁ : ∀ a b, P₁ a ⊗ P₁ b ⟶ P₁ (a + b)} {η₁ : 𝟙_ C ⟶ P₁ 0}
    {P₂ : (Fin r → ℕ) → C} {μ₂ : ∀ a b, P₂ a ⊗ P₂ b ⟶ P₂ (a + b)} {η₂ : 𝟙_ C ⟶ P₂ 0}
    {w₁ : ℕ → κ} {hw₁ : ∀ a b, w₁ (a + b) = w₁ a + w₁ b} {hw₁0 : w₁ 0 = 0} {Ψ₁ : ∀ a, P₁ a ⟶ Q (w₁ a)}
    {w₂ : (Fin r → ℕ) → κ} {hw₂ : ∀ a b, w₂ (a + b) = w₂ a + w₂ b} {hw₂0 : w₂ 0 = 0}
    {Ψ₂ : ∀ a, P₂ a ⟶ Q (w₂ a)}
    (h₁ : IsGradedMonoidHom P₁ μ₁ η₁ Q ν θ w₁ hw₁ hw₁0 Ψ₁)
    (h₂ : IsGradedMonoidHom P₂ μ₂ η₂ Q ν θ w₂ hw₂ hw₂0 Ψ₂)
    (hw : ∀ d d' : Fin (r + 1) → ℕ,
      w₁ ((d + d') 0) + w₂ (Fin.tail (d + d')) = (w₁ (d 0) + w₂ (Fin.tail d)) + (w₁ (d' 0) + w₂ (Fin.tail d')))
    (hw0 : w₁ ((0 : Fin (r + 1) → ℕ) 0) + w₂ (Fin.tail (0 : Fin (r + 1) → ℕ)) = 0) :
    IsGradedMonoidHom (fun d : Fin (r + 1) → ℕ => P₁ (d 0) ⊗ P₂ (Fin.tail d))
      (fun d d' => tensorμ (P₁ (d 0)) (P₂ (Fin.tail d)) (P₁ (d' 0)) (P₂ (Fin.tail d')) ≫
        (μ₁ (d 0) (d' 0) ⊗ₘ μ₂ (Fin.tail d) (Fin.tail d')))
      ((λ_ (𝟙_ C)).inv ≫ (η₁ ⊗ₘ η₂)) Q ν θ
      (fun d => w₁ (d 0) + w₂ (Fin.tail d)) hw hw0
      (fun d => (Ψ₁ (d 0) ⊗ₘ Ψ₂ (Fin.tail d)) ≫ ν _ _) where
  map_mul d d' := by
    have e₁ : w₁ (d 0) + w₁ (d' 0) = w₁ (d 0 + d' 0) := (hw₁ _ _).symm
    have e₂ : w₂ (Fin.tail d) + w₂ (Fin.tail d') = w₂ (Fin.tail d + Fin.tail d') :=
      (hw₂ _ _).symm
    have e₃ : w₁ (d 0) + w₂ (Fin.tail d) + (w₁ (d' 0) + w₂ (Fin.tail d')) =
        w₁ (d 0 + d' 0) + w₂ (Fin.tail d + Fin.tail d') := by
      rw [← e₁, ← e₂, add_add_add_comm]
    show (tensorμ _ _ _ _ ≫ (μ₁ (d 0) (d' 0) ⊗ₘ μ₂ (Fin.tail d) (Fin.tail d'))) ≫
        ((Ψ₁ (d 0 + d' 0) ⊗ₘ Ψ₂ (Fin.tail d + Fin.tail d')) ≫ ν _ _) =
      (((Ψ₁ (d 0) ⊗ₘ Ψ₂ (Fin.tail d)) ≫ ν _ _) ⊗ₘ ((Ψ₁ (d' 0) ⊗ₘ Ψ₂ (Fin.tail d')) ≫ ν _ _)) ≫
        gmul Q ν e₃
    rw [Category.assoc, ← Category.assoc (μ₁ _ _ ⊗ₘ μ₂ _ _), tensorHom_comp_tensorHom, h₁.map_mul,
      h₂.map_mul, ← tensorHom_comp_tensorHom, Category.assoc, ← tensorμ_natural_assoc,
      ← gmul_rfl Q ν (w₁ (d 0 + d' 0)) (w₂ (Fin.tail d + Fin.tail d')),
      hQ.gmul_interchange e₁ e₂ rfl rfl rfl e₃, ← gmul_rfl Q ν (w₁ (d 0)) (w₂ (Fin.tail d)),
      ← gmul_rfl Q ν (w₁ (d' 0)) (w₂ (Fin.tail d')), ← tensorHom_comp_tensorHom, Category.assoc]
  map_one := by
    have e₀ : (0 : κ) = w₁ 0 + w₂ 0 := by rw [hw₁0, hw₂0, add_zero]
    dsimp only [Pi.zero_apply, tail_zero']
    rw [Category.assoc, ← Category.assoc (η₁ ⊗ₘ η₂), tensorHom_comp_tensorHom, h₁.map_one, h₂.map_one,
      ← tensorHom_comp_tensorHom, Category.assoc, ← gmul_rfl Q ν (w₁ 0) (w₂ 0),
      eqToHom_tensorHom_comp_gmul Q ν hw₁0.symm hw₂0.symm rfl,
      hQ.tensorHom_one_one_comp_gmul (by rw [hw₁0, hw₂0, add_zero]) e₀, Iso.inv_hom_id_assoc]

end IsGradedMonoidHom

end Hom

end MiyaokaMori
