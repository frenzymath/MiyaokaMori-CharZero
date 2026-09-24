import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.Algebra.GradedMonoidTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure

/-! # The weighted symmetric algebra sheaf

The weighted symmetric algebra: for a family of locally free sheaves `V_0, …, V_{r−1}`, take
`Sym(V_0^∨ ⊕ ⋯ ⊕ V_{r−1}^∨)` with `V_q^∨` in weight `q+1`. The convention follows the
"projectivization of lines" of the paper: coordinate functions take values in `V^∨`, and `Proj`
parametrizes (weighted) lines in the fibres, so the generators are `V_q^∨`, not `V_q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- `⊗_{q<r} Sym^{d q}(W q)`, defined by recursion on `Fin r` (`𝟙 = O_X` for `r = 0`). -/

noncomputable def AlgebraicGeometry.Scheme.weightedSymTensor {X : AlgebraicGeometry.Scheme.{u}} :
    (r : ℕ) → (Fin r → X.Modules) → (Fin r → ℕ) → X.Modules
  | 0, _, _ => 𝟙_ X.Modules
  | r + 1, W, d =>
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).part (d 0) ⊗
        AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail W) (Fin.tail d)

/-- The factorwise multiplication `(⊗_q Sym^{d q}) ⊗ (⊗_q Sym^{d' q}) → ⊗_q Sym^{d q + d' q}`: rearrange with
`tensorμ`, then multiply in each `Sym(W q)`. -/

noncomputable def AlgebraicGeometry.Scheme.weightedSymTensorMul {X : AlgebraicGeometry.Scheme.{u}} :
    (r : ℕ) → (W : Fin r → X.Modules) → (d d' : Fin r → ℕ) →
      (AlgebraicGeometry.Scheme.weightedSymTensor r W d ⊗ AlgebraicGeometry.Scheme.weightedSymTensor r W d' ⟶
        AlgebraicGeometry.Scheme.weightedSymTensor r W (d + d'))
  | 0, _, _, _ => (λ_ (𝟙_ X.Modules)).hom
  | r + 1, W, d, d' =>
      CategoryTheory.MonoidalCategory.tensorμ _ _ _ _ ≫
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).mul (d 0) (d' 0) ⊗ₘ
          AlgebraicGeometry.Scheme.weightedSymTensorMul r (Fin.tail W) (Fin.tail d) (Fin.tail d'))

/-- The unit `O_X → ⊗_q Sym^0(W q)`. -/

noncomputable def AlgebraicGeometry.Scheme.weightedSymTensorOne {X : AlgebraicGeometry.Scheme.{u}} :
    (r : ℕ) → (W : Fin r → X.Modules) →
      (𝟙_ X.Modules ⟶ AlgebraicGeometry.Scheme.weightedSymTensor r W 0)
  | 0, _ => 𝟙 _
  | r + 1, W =>
      (λ_ (𝟙_ X.Modules)).inv ≫
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).one ⊗ₘ
          AlgebraicGeometry.Scheme.weightedSymTensorOne r (Fin.tail W))

/-- Multi-degrees of weight `m`: `d : Fin r → Fin (m+1)` with `Σ_q (q+1)·d_q = m` (a finite set). -/

abbrev AlgebraicGeometry.Scheme.weightedSymIndex (r m : ℕ) : Type :=
  { d : Fin r → Fin (m + 1) // ∑ q : Fin r, ((q : ℕ) + 1) * (d q : ℕ) = m }

/-- Addition of multi-degrees: `D_m × D_n → D_{m+n}`. -/

def AlgebraicGeometry.Scheme.weightedSymIndex.add {r m n : ℕ}
    (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) (d' : AlgebraicGeometry.Scheme.weightedSymIndex r n) :
    AlgebraicGeometry.Scheme.weightedSymIndex r (m + n) :=
  ⟨fun q => ⟨(d.1 q : ℕ) + d'.1 q, by have := (d.1 q).2; have := (d'.1 q).2; omega⟩, by
    simp only [mul_add, Finset.sum_add_distrib, d.2, d'.2]⟩

/-- The generating sheaves `W_q := V_q^∨` (the "projectivization of lines" convention). -/

noncomputable abbrev AlgebraicGeometry.Scheme.weightedSymAlgebra.gen {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) : Fin r → X.Modules :=
  fun q => AlgebraicGeometry.Scheme.Modules.dual (V q)

/-- T_d := ⊗_q Sym^{d_q}(W_q) -/

noncomputable abbrev AlgebraicGeometry.Scheme.weightedSymAlgebra.term {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) : X.Modules :=
  AlgebraicGeometry.Scheme.weightedSymTensor r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) (fun q => (d.1 q : ℕ))

/-- part m := ⨁_{d ∈ D_m} T_d -/

noncomputable abbrev AlgebraicGeometry.Scheme.weightedSymAlgebra.part {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) (m : ℕ) : X.Modules :=
  CategoryTheory.Limits.biproduct fun d : AlgebraicGeometry.Scheme.weightedSymIndex r m => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d

/-- mul = Σ_{d,d'} (π_d ⊗ π_{d'}) ≫ (T_d ⊗ T_{d'} → T_{d+d'}) ≫ ι_{d+d'} -/

noncomputable def AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) (m n : ℕ) :
    AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V n ⟶ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V (m + n) :=
  ∑ p : AlgebraicGeometry.Scheme.weightedSymIndex r m × AlgebraicGeometry.Scheme.weightedSymIndex r n,
    (CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) p.1 ⊗ₘ
        CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) p.2) ≫
      AlgebraicGeometry.Scheme.weightedSymTensorMul r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) _ _ ≫
      CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) (p.1.add p.2)

noncomputable def AlgebraicGeometry.Scheme.weightedSymAlgebra.oneHom {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) : 𝟙_ X.Modules ⟶ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V 0 :=
  AlgebraicGeometry.Scheme.weightedSymTensorOne r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) ≫
    CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) (⟨0, by simp⟩ : AlgebraicGeometry.Scheme.weightedSymIndex r 0)

/- The four proof obligations of `weightedSymAlgebra` (quasi-coherence of the pieces and the three algebra
   laws) are stated as named theorems below; see their docstrings and `weightedSymTensor_isGradedMonoid`. -/

namespace AlgebraicGeometry.Scheme

open CategoryTheory.MonoidalCategory

section Recursive
variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The three axioms of `GradedQCAlgebra` are exactly `IsGradedMonoid` (with `ι = ℕ`). -/
theorem GradedQCAlgebra.isGradedMonoid (S : X.GradedQCAlgebra) :
    MiyaokaMori.IsGradedMonoid S.part S.mul S.one :=
  ⟨S.one_mul, S.mul_assoc, S.mul_comm⟩

/-- **The three axioms of the recursive layer**: `⊗_{q<r} Sym^{d q}(W q)` with `weightedSymTensorMul`,
`weightedSymTensorOne` is a commutative monoid graded by `Fin r → ℕ`. By induction on `r`: `r = 0` is the
trivial graded monoid `IsGradedMonoid.unit`; `r + 1` is the tensor product `IsGradedMonoid.consTensor` of
`symGradedAlgebra (W 0)` (either branch of the `dite` is a `GradedQCAlgebra`, so its axioms apply) with the
recursive layer (`IsGradedMonoid.tensor` indexed by `d ↦ (d 0, Fin.tail d)`, the `Fin (r+1) → ℕ` version;
`weightedSymTensor (r+1)`, `weightedSymTensorMul (r+1)`, `weightedSymTensorOne (r+1)` are by definition its
data). -/
theorem weightedSymTensor_isGradedMonoid : ∀ (r : ℕ) (W : Fin r → X.Modules),
    MiyaokaMori.IsGradedMonoid (AlgebraicGeometry.Scheme.weightedSymTensor r W)
      (AlgebraicGeometry.Scheme.weightedSymTensorMul r W)
      (AlgebraicGeometry.Scheme.weightedSymTensorOne r W)
  | 0, _ => MiyaokaMori.IsGradedMonoid.unit
  | r + 1, W =>
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).isGradedMonoid.consTensor
      (weightedSymTensor_isGradedMonoid r (Fin.tail W))

/-- Each piece of the recursive layer is quasi-coherent: `r = 0` is `O_X`; `r + 1` is the tensor product of
`Sym^{d 0}(W 0)` (a field of `GradedQCAlgebra`) with the recursive layer (Stacks 01CE). -/
theorem weightedSymTensor_isQuasicoherent : ∀ (r : ℕ) (W : Fin r → X.Modules) (d : Fin r → ℕ),
    (AlgebraicGeometry.Scheme.weightedSymTensor r W d).IsQuasicoherent
  | 0, _, _ => AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent X
  | r + 1, W, d =>
    AlgebraicGeometry.Scheme.Modules.tensorObj_isQuasicoherent _ _
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).quasicoherent (d 0))
      (weightedSymTensor_isQuasicoherent r (Fin.tail W) (Fin.tail d))

end Recursive

namespace weightedSymIndex
variable {r : ℕ}

theorem ext' {m : ℕ} {d d' : AlgebraicGeometry.Scheme.weightedSymIndex r m}
    (h : ∀ q, (d.1 q : ℕ) = d'.1 q) : d = d' :=
  Subtype.ext (funext fun q => Fin.ext (h q))

/-- The only multi-degree of weight `0` is `0`. -/
theorem eq_zero (d : AlgebraicGeometry.Scheme.weightedSymIndex r 0) :
    d = ⟨0, by simp⟩ := by
  apply ext'
  intro q
  have h := d.2
  rw [Finset.sum_eq_zero_iff] at h
  simpa using h q (Finset.mem_univ q)

theorem add_val {m n : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (d' : AlgebraicGeometry.Scheme.weightedSymIndex r n) (q : Fin r) :
    ((d.add d').1 q : ℕ) = d.1 q + d'.1 q := rfl

end weightedSymIndex

namespace weightedSymAlgebra
variable {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ} (V : Fin r → X.Modules)

/-- The value of a multi-degree (in `Fin r → ℕ`). -/
abbrev dv {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) : Fin r → ℕ :=
  fun q => (d.1 q : ℕ)

/-- `T_a ⊗ T_b → T_{a+b}`: `weightedSymTensorMul` indexed by `weightedSymIndex`, a **well-typed wrapper**
(in the definition of `mulHom`, `weightedSymTensorMul … ≫ ι_{a.add b}` is only well-typed after unfolding
`weightedSymIndex.add`, and `rw` / `slice` refuse to rearrange it at reducible transparency; with this
wrapper every composite at the biproduct level is well-typed). -/
def mulTerm {m n : ℕ} (a : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (b : AlgebraicGeometry.Scheme.weightedSymIndex r n) :
    AlgebraicGeometry.Scheme.weightedSymAlgebra.term V a ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.term V b ⟶ AlgebraicGeometry.Scheme.weightedSymAlgebra.term V (a.add b) :=
  AlgebraicGeometry.Scheme.weightedSymTensorMul r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) (dv a) (dv b)

/-- Two indices with the same multi-degree value give the same `T` (only the weight label differs). -/
theorem term_congr {m n : ℕ} {d : AlgebraicGeometry.Scheme.weightedSymIndex r m}
    {d' : AlgebraicGeometry.Scheme.weightedSymIndex r n} (hd : ∀ q, (d.1 q : ℕ) = d'.1 q) :
    AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d = AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d' :=
  congrArg (AlgebraicGeometry.Scheme.weightedSymTensor r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V))
    (funext hd)

theorem zero_add_val {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) (q : Fin r) :
    (d.1 q : ℕ) = ((AlgebraicGeometry.Scheme.weightedSymIndex.add
      (⟨0, by simp⟩ : AlgebraicGeometry.Scheme.weightedSymIndex r 0) d).1 q : ℕ) := by
  simp [weightedSymIndex.add_val]

theorem add_assoc_val {m n l : ℕ} (a : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (b : AlgebraicGeometry.Scheme.weightedSymIndex r n) (c : AlgebraicGeometry.Scheme.weightedSymIndex r l)
    (q : Fin r) : (((a.add b).add c).1 q : ℕ) = ((a.add (b.add c)).1 q : ℕ) := by
  simp [weightedSymIndex.add_val, Nat.add_assoc]

theorem add_comm_val {m n : ℕ} (a : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (b : AlgebraicGeometry.Scheme.weightedSymIndex r n) (q : Fin r) :
    ((a.add b).1 q : ℕ) = ((b.add a).1 q : ℕ) := by
  simp [weightedSymIndex.add_val, Nat.add_comm]

/-- The left unit law of the recursive layer, stated with `mulTerm` (definitionally the `one_mul` of
`weightedSymTensor_isGradedMonoid`). -/
theorem mulTerm_one_mul {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) :
    (AlgebraicGeometry.Scheme.weightedSymTensorOne r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) ▷ AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) ≫
        mulTerm V (⟨0, by simp⟩ : AlgebraicGeometry.Scheme.weightedSymIndex r 0) d =
      (λ_ (AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d)).hom ≫ eqToHom (term_congr V (zero_add_val d)) :=
  (AlgebraicGeometry.Scheme.weightedSymTensor_isGradedMonoid r
    (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V)).one_mul (dv d)

/-- Associativity of the recursive layer, stated with `mulTerm`. -/
theorem mulTerm_assoc {m n l : ℕ} (a : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (b : AlgebraicGeometry.Scheme.weightedSymIndex r n) (c : AlgebraicGeometry.Scheme.weightedSymIndex r l) :
    (α_ (AlgebraicGeometry.Scheme.weightedSymAlgebra.term V a) (AlgebraicGeometry.Scheme.weightedSymAlgebra.term V b) (AlgebraicGeometry.Scheme.weightedSymAlgebra.term V c)).hom ≫ (AlgebraicGeometry.Scheme.weightedSymAlgebra.term V a ◁ mulTerm V b c) ≫ mulTerm V a (b.add c) =
      (mulTerm V a b ▷ AlgebraicGeometry.Scheme.weightedSymAlgebra.term V c) ≫ mulTerm V (a.add b) c ≫ eqToHom (term_congr V (add_assoc_val a b c)) :=
  (AlgebraicGeometry.Scheme.weightedSymTensor_isGradedMonoid r
    (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V)).mul_assoc (dv a) (dv b) (dv c)

/-- Commutativity of the recursive layer, stated with `mulTerm`. -/
theorem mulTerm_comm {m n : ℕ} (a : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (b : AlgebraicGeometry.Scheme.weightedSymIndex r n) :
    (β_ (AlgebraicGeometry.Scheme.weightedSymAlgebra.term V a) (AlgebraicGeometry.Scheme.weightedSymAlgebra.term V b)).hom ≫ mulTerm V b a = mulTerm V a b ≫ eqToHom (term_congr V (add_comm_val a b)) :=
  (AlgebraicGeometry.Scheme.weightedSymTensor_isGradedMonoid r
    (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V)).mul_comm (dv a) (dv b)

/-- `eqToHom ≫ ι_{d'} = ι_d ≫ eqToHom` when `d`, `d'` have the same value (only the weight labels `m = n`
differ). -/
theorem eqToHom_comp_ι {m n : ℕ} (h : m = n) {d : AlgebraicGeometry.Scheme.weightedSymIndex r m}
    {d' : AlgebraicGeometry.Scheme.weightedSymIndex r n} (hd : ∀ q, (d.1 q : ℕ) = d'.1 q) :
    eqToHom (term_congr V hd) ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) d' = CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) d ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V) h) := by
  subst h
  obtain rfl : d = d' := weightedSymIndex.ext' hd
  simp

/-- **Components of the multiplication**: `(ι_a ⊗ ι_b) ≫ mul = mulTerm a b ≫ ι_{a+b}` (the biproduct
components are orthogonal; this needs that `⊗` preserves zero). -/
theorem ι_tensor_ι_comp_mulHom {m n : ℕ} (a : AlgebraicGeometry.Scheme.weightedSymIndex r m)
    (b : AlgebraicGeometry.Scheme.weightedSymIndex r n) :
    (CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a ⊗ₘ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b) ≫ AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V m n =
      mulTerm V a b ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) (a.add b) := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  unfold AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom
  simp only [Preadditive.comp_sum, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · rw [← Category.assoc, tensorHom_comp_tensorHom, CategoryTheory.Limits.biproduct.ι_π_self,
      CategoryTheory.Limits.biproduct.ι_π_self, id_tensorHom_id, Category.id_comp]
    rfl
  · intro b' _ hb'
    rw [← Category.assoc, tensorHom_comp_tensorHom, CategoryTheory.Limits.biproduct.ι_π_ne _ (Ne.symm hb'),
      MonoidalPreadditive.tensor_zero, zero_comp]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro b' _
    rw [← Category.assoc, tensorHom_comp_tensorHom, CategoryTheory.Limits.biproduct.ι_π_ne _ (Ne.symm ha'),
      MonoidalPreadditive.zero_tensor, zero_comp]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Morphisms out of `𝟙_ ⊗ part m` are determined by the `𝟙_ ◁ ι_d`. -/
theorem ext₁ {m : ℕ} {Y : X.Modules} {g h : 𝟙_ X.Modules ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⟶ Y}
    (w : ∀ d, (𝟙_ X.Modules ◁ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) d) ≫ g = (𝟙_ X.Modules ◁ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) d) ≫ h) : g = h := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  have e : ∀ k : 𝟙_ X.Modules ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⟶ Y, k = (𝟙_ X.Modules ◁ ∑ d, CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) d ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) d) ≫ k := by
    intro k
    rw [CategoryTheory.Limits.biproduct.total, whiskerLeft_id, Category.id_comp]
  rw [e g, e h]
  simp only [whiskerLeft_sum, whiskerLeft_comp, Preadditive.sum_comp, Category.assoc, w]

/-- Morphisms out of `part m ⊗ part n` are determined by the `ι_a ⊗ ι_b`. -/
theorem ext₂ {m n : ℕ} {Y : X.Modules} {g h : AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V n ⟶ Y}
    (w : ∀ a b, (CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a ⊗ₘ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b) ≫ g = (CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a ⊗ₘ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b) ≫ h) : g = h := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  have e : ∀ k : AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V n ⟶ Y,
      k = ((∑ a, CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a) ⊗ₘ (∑ b, CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b)) ≫ k := by
    intro k
    rw [CategoryTheory.Limits.biproduct.total, CategoryTheory.Limits.biproduct.total, id_tensorHom_id,
      Category.id_comp]
  rw [e g, e h]
  simp only [sum_tensor, tensor_sum, Preadditive.sum_comp, ← tensorHom_comp_tensorHom, Category.assoc, w]

/-- Morphisms out of `(part m ⊗ part n) ⊗ part l` are determined by the `(ι_a ⊗ ι_b) ⊗ ι_c`. -/
theorem ext₃ {m n l : ℕ} {Y : X.Modules} {g h : (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V n) ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V l ⟶ Y}
    (w : ∀ a b c, ((CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a ⊗ₘ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b) ⊗ₘ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) c) ≫ g = ((CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a ⊗ₘ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b) ⊗ₘ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) c) ≫ h) : g = h := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  have e : ∀ k : (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V n) ⊗ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V l ⟶ Y,
      k = (((∑ a, CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) a) ⊗ₘ (∑ b, CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) b)) ⊗ₘ (∑ c, CategoryTheory.Limits.biproduct.π (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) c ≫ CategoryTheory.Limits.biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) c)) ≫ k := by
    intro k
    rw [CategoryTheory.Limits.biproduct.total, CategoryTheory.Limits.biproduct.total,
      CategoryTheory.Limits.biproduct.total, id_tensorHom_id, id_tensorHom_id, Category.id_comp]
  rw [e g, e h]
  simp only [sum_tensor, tensor_sum, Preadditive.sum_comp, ← tensorHom_comp_tensorHom, Category.assoc, w]

end weightedSymAlgebra

end AlgebraicGeometry.Scheme

/-- The graded pieces are quasi-coherent. Each factor `(symGradedAlgebra (W q)).part e` is quasi-coherent as a
field of `GradedQCAlgebra` (both branches of the `dite` are `GradedQCAlgebra`s); `𝟙_ = O_X` is quasi-coherent
(`O_X ≅ free PUnit` is locally free); tensor products preserve quasi-coherence (Stacks 01CE); finite biproducts
preserve quasi-coherence (`isQuasicoherent_biproduct_of_fintype`, via `isQuasicoherent_colimit`). The
instance hypotheses `[IsLocallyFree]`, `[IsFiniteType]` are not needed in this proof (kept in the signature
for the call sites). -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra.part_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree]
    [∀ q, (V q).IsFiniteType] (m : ℕ) : (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct_of_fintype _ fun _ =>
    AlgebraicGeometry.Scheme.weightedSymTensor_isQuasicoherent r _ _

/-- Left unit law. Proof: `ext₁` reduces to the components `𝟙_ ◁ ι_d`;
`(𝟙_ ◁ ι_d) ≫ (one ▷ part m) = one ⊗ ι_d = (θ ▷ T_d) ≫ (ι_0 ⊗ ι_d)`; use `ι_tensor_ι_comp_mulHom` and the
`one_mul` of the recursive layer (`mulTerm_one_mul`), and finally `eqToHom_comp_ι` replaces `ι_{0+d}` by
`ι_d ≫ eqToHom`; the right side uses naturality of the left unitor. -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra.one_mul {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) (m : ℕ) :
    (AlgebraicGeometry.Scheme.weightedSymAlgebra.oneHom V ▷ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m) ≫ AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V 0 m =
      (λ_ (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m)).hom ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V) (Nat.zero_add m).symm) := by
  open AlgebraicGeometry.Scheme.weightedSymAlgebra in
  open CategoryTheory.MonoidalCategory in
  apply ext₁
  intro d
  slice_lhs 1 2 => rw [← tensorHom_def']
  rw [oneHom, ← whiskerRight_comp_tensorHom, Category.assoc, ι_tensor_ι_comp_mulHom]
  slice_lhs 1 2 => rw [mulTerm_one_mul]
  simp only [Category.assoc]
  rw [eqToHom_comp_ι V (Nat.zero_add m).symm (zero_add_val d), leftUnitor_naturality_assoc]

/-- Associativity. Proof: `ext₃` reduces to the components `(ι_a ⊗ ι_b) ⊗ ι_c`; both sides are turned into the
multiplication `mulTerm` of the recursive layer by `ι_tensor_ι_comp_mulHom` (twice), then use the `mul_assoc`
of the recursive layer (`mulTerm_assoc`) and finally `eqToHom_comp_ι`. -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra.mul_assoc {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) (m n l : ℕ) :
    (α_ (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m) (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V n) (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V l)).hom ≫
        (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ◁ AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V n l) ≫ AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V m (n + l) =
      (AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V m n ▷ AlgebraicGeometry.Scheme.weightedSymAlgebra.part V l) ≫ AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V (m + n) l ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V) (Nat.add_assoc m n l)) := by
  open AlgebraicGeometry.Scheme.weightedSymAlgebra in
  open CategoryTheory.MonoidalCategory in
  apply ext₃
  intro a b c
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 => rw [tensorHom_comp_whiskerLeft, ι_tensor_ι_comp_mulHom, ← whiskerLeft_comp_tensorHom]
  slice_lhs 3 4 => rw [ι_tensor_ι_comp_mulHom]
  slice_lhs 1 3 => rw [mulTerm_assoc]
  slice_lhs 3 4 => rw [eqToHom_comp_ι V (Nat.add_assoc m n l) (add_assoc_val a b c)]
  slice_rhs 1 2 => rw [tensorHom_comp_whiskerRight, ι_tensor_ι_comp_mulHom, ← whiskerRight_comp_tensorHom]
  slice_rhs 2 3 => rw [ι_tensor_ι_comp_mulHom]
  simp only [Category.assoc]

/-- Commutativity. Proof: `ext₂` reduces to the components `ι_a ⊗ ι_b`; naturality of the braiding moves
`ι_a ⊗ ι_b` to the right of the braiding; use `ι_tensor_ι_comp_mulHom` and the `mul_comm` of the recursive
layer (`mulTerm_comm`), and finally `eqToHom_comp_ι`. -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra.mul_comm {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) (m n : ℕ) :
    (β_ (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m) (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V n)).hom ≫ AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V n m =
      AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V m n ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedSymAlgebra.part V) (Nat.add_comm m n)) := by
  open AlgebraicGeometry.Scheme.weightedSymAlgebra in
  open CategoryTheory.MonoidalCategory in
  apply ext₂
  intro a b
  slice_lhs 1 2 => rw [BraidedCategory.braiding_naturality]
  slice_lhs 2 3 => rw [ι_tensor_ι_comp_mulHom]
  slice_lhs 1 2 => rw [mulTerm_comm]
  slice_lhs 2 3 => rw [eqToHom_comp_ι V (Nat.add_comm m n) (add_comm_val a b)]
  slice_rhs 1 2 => rw [ι_tensor_ι_comp_mulHom]
  simp only [Category.assoc]

noncomputable def AlgebraicGeometry.Scheme.weightedSymAlgebra {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree]
    [∀ q, (V q).IsFiniteType] : X.GradedQCAlgebra where
  part := AlgebraicGeometry.Scheme.weightedSymAlgebra.part V
  quasicoherent := AlgebraicGeometry.Scheme.weightedSymAlgebra.part_isQuasicoherent V
  mul := AlgebraicGeometry.Scheme.weightedSymAlgebra.mulHom V
  one := AlgebraicGeometry.Scheme.weightedSymAlgebra.oneHom V
  one_mul := AlgebraicGeometry.Scheme.weightedSymAlgebra.one_mul V
  mul_assoc := AlgebraicGeometry.Scheme.weightedSymAlgebra.mul_assoc V
  mul_comm := AlgebraicGeometry.Scheme.weightedSymAlgebra.mul_comm V

end
