import MiyaokaMori.Prelude

/-! # The long exact `Ext` sequence is linear for a postcomposition action

Let `C` be an abelian category with `Ext`, `A : C`, and `R` a semiring. Suppose the `R`-module
structure on `Ext^n(A, B)` is given by postcomposition with a family of endomorphisms `μ_B(r)` of `B`
(`r • x = x ∘ μ_B(r)`). Then:
(a) a morphism `f : B ⟶ B'` commuting with `μ` induces an `R`-linear map `Ext^n(A, B) → Ext^n(A, B')`,
functorially;
(b) for a short exact sequence `S` with `μ_1, μ_2, μ_3` commuting with `S.f`, `S.g`, the connecting
map `Ext^n(A, S.X₃) → Ext^{n+1}(A, S.X₁)` (postcomposition with the extension class) is `R`-linear;
(c) the long exact sequence satisfies `LinearMap.range = LinearMap.ker` at every place.

Proof:
1. (a): `f_*(r • x) = (x ∘ μ_B(r)) ∘ f = x ∘ (μ_B(r) ≫ f) = x ∘ (f ≫ μ_{B'}(r)) = r • f_*(x)`, using
   `Ext.comp_assoc_of_third_deg_zero` and `Ext.mk₀_comp_mk₀`; additivity is `Ext.add_comp`.
2. (b): `(μ_1(r), μ_2(r), μ_3(r))` is an endomorphism of the short complex `S`, and
   `ShortComplex.ShortExact.extClass_naturality` gives `extClass ∘ μ_1(r) = μ_3(r) ∘ extClass`; then
   associativity of the composition of `Ext`.
3. (c): "image ⊆ kernel" comes from `S.zero`, `comp_extClass`, `extClass_comp`; "kernel ⊆ image" is
   `Ext.covariant_sequence_exact₁/₂/₃`.

The statement is made over a general category because for the concrete instance `HasExt.standard`
the kernel is very slow at checking definitional equality between two projection paths in
`AddCommGroup`; over a general category this does not occur, and the concrete case only instantiates.

Reference: the linearization of Mathlib's `Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean`.
Used for the `K`-linear version of the long exact cohomology sequence.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe w v u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {R : Type*} [Semiring R] {A : C}

/-- The `R`-linear map `Ext^n(A, B) → Ext^n(A, B')` induced by an `f` commuting with the action `μ`. -/
def postcompLinear {B B' : C} {n : ℕ} [Module R (Ext A B n)] [Module R (Ext A B' n)]
    (μ : R → (B ⟶ B)) (μ' : R → (B' ⟶ B'))
    (hB : ∀ (r : R) (x : Ext A B n), r • x = x.comp (mk₀ (μ r)) (add_zero n))
    (hB' : ∀ (r : R) (x : Ext A B' n), r • x = x.comp (mk₀ (μ' r)) (add_zero n))
    (f : B ⟶ B') (hf : ∀ r, μ r ≫ f = f ≫ μ' r) :
    Ext A B n →ₗ[R] Ext A B' n where
  toFun x := x.comp (mk₀ f) (add_zero n)
  map_add' x y := add_comp x y _ _
  map_smul' r x := by
    simp only [hB, hB', RingHom.id_apply, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, hf]

/-- The `R`-linear version of the connecting map (postcomposition with the extension class). -/
def extClassLinear {S : ShortComplex C} (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    [Module R (Ext A S.X₃ n₀)] [Module R (Ext A S.X₁ n₁)]
    (μ₁ : R → (S.X₁ ⟶ S.X₁)) (μ₂ : R → (S.X₂ ⟶ S.X₂)) (μ₃ : R → (S.X₃ ⟶ S.X₃))
    (h₃ : ∀ (r : R) (x : Ext A S.X₃ n₀), r • x = x.comp (mk₀ (μ₃ r)) (add_zero n₀))
    (h₁ : ∀ (r : R) (x : Ext A S.X₁ n₁), r • x = x.comp (mk₀ (μ₁ r)) (add_zero n₁))
    (hf : ∀ r, μ₁ r ≫ S.f = S.f ≫ μ₂ r) (hg : ∀ r, μ₂ r ≫ S.g = S.g ≫ μ₃ r) :
    Ext A S.X₃ n₀ →ₗ[R] Ext A S.X₁ n₁ where
  toFun x := x.comp hS.extClass h
  map_add' x y := add_comp x y _ _
  map_smul' r x := by
    have nat := ShortComplex.ShortExact.extClass_naturality hS hS
      (ShortComplex.Hom.mk (μ₁ r) (μ₂ r) (μ₃ r) (hf r) (hg r))
    dsimp only at nat
    simp only [h₃, h₁, RingHom.id_apply, comp_assoc_of_second_deg_zero,
      comp_assoc_of_third_deg_zero, nat]

section Apply

variable {B B' : C} {n : ℕ} [Module R (Ext A B n)] [Module R (Ext A B' n)]
    (μ : R → (B ⟶ B)) (μ' : R → (B' ⟶ B'))
    (hB : ∀ (r : R) (x : Ext A B n), r • x = x.comp (mk₀ (μ r)) (add_zero n))
    (hB' : ∀ (r : R) (x : Ext A B' n), r • x = x.comp (mk₀ (μ' r)) (add_zero n))

@[simp]
theorem postcompLinear_apply (f : B ⟶ B') (hf : ∀ r, μ r ≫ f = f ≫ μ' r) (x : Ext A B n) :
    postcompLinear μ μ' hB hB' f hf x = x.comp (mk₀ f) (add_zero n) := rfl

theorem postcompLinear_id :
    postcompLinear μ μ hB hB (𝟙 B) (fun r => by simp) = LinearMap.id := by
  ext x; simp

theorem postcompLinear_comp {B'' : C} [Module R (Ext A B'' n)] (μ'' : R → (B'' ⟶ B''))
    (hB'' : ∀ (r : R) (x : Ext A B'' n), r • x = x.comp (mk₀ (μ'' r)) (add_zero n))
    (f : B ⟶ B') (hf : ∀ r, μ r ≫ f = f ≫ μ' r) (g : B' ⟶ B'') (hg : ∀ r, μ' r ≫ g = g ≫ μ'' r) :
    postcompLinear μ μ'' hB hB'' (f ≫ g)
        (fun r => by rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]) =
      (postcompLinear μ' μ'' hB' hB'' g hg).comp (postcompLinear μ μ' hB hB' f hf) := by
  ext x; simp

theorem postcompLinear_add (f g : B ⟶ B') (hf : ∀ r, μ r ≫ f = f ≫ μ' r)
    (hg : ∀ r, μ r ≫ g = g ≫ μ' r) :
    postcompLinear μ μ' hB hB' (f + g)
        (fun r => by rw [Preadditive.comp_add, Preadditive.add_comp, hf, hg]) =
      postcompLinear μ μ' hB hB' f hf + postcompLinear μ μ' hB hB' g hg := by
  ext x; simp [mk₀_add]

end Apply

section Exact

variable {S : ShortComplex C} (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    [Module R (Ext A S.X₁ n₀)] [Module R (Ext A S.X₂ n₀)] [Module R (Ext A S.X₃ n₀)]
    [Module R (Ext A S.X₁ n₁)] [Module R (Ext A S.X₂ n₁)]
    (μ₁ : R → (S.X₁ ⟶ S.X₁)) (μ₂ : R → (S.X₂ ⟶ S.X₂)) (μ₃ : R → (S.X₃ ⟶ S.X₃))
    (h₁₀ : ∀ (r : R) (x : Ext A S.X₁ n₀), r • x = x.comp (mk₀ (μ₁ r)) (add_zero n₀))
    (h₂₀ : ∀ (r : R) (x : Ext A S.X₂ n₀), r • x = x.comp (mk₀ (μ₂ r)) (add_zero n₀))
    (h₃₀ : ∀ (r : R) (x : Ext A S.X₃ n₀), r • x = x.comp (mk₀ (μ₃ r)) (add_zero n₀))
    (h₁₁ : ∀ (r : R) (x : Ext A S.X₁ n₁), r • x = x.comp (mk₀ (μ₁ r)) (add_zero n₁))
    (h₂₁ : ∀ (r : R) (x : Ext A S.X₂ n₁), r • x = x.comp (mk₀ (μ₂ r)) (add_zero n₁))
    (hf : ∀ r, μ₁ r ≫ S.f = S.f ≫ μ₂ r) (hg : ∀ r, μ₂ r ≫ S.g = S.g ≫ μ₃ r)

omit [Module R (Ext A S.X₁ n₀)] [Module R (Ext A S.X₂ n₀)] [Module R (Ext A S.X₂ n₁)] in
@[simp]
theorem extClassLinear_apply (x : Ext A S.X₃ n₀) :
    extClassLinear hS h μ₁ μ₂ μ₃ h₃₀ h₁₁ hf hg x = x.comp hS.extClass h := rfl

include hS in
/-- Exactness of the long exact sequence at `Ext^n(A, S.X₂)`. -/
theorem range_postcompLinear_f_eq_ker_g :
    LinearMap.range (postcompLinear μ₁ μ₂ h₁₀ h₂₀ S.f hf) =
      LinearMap.ker (postcompLinear μ₂ μ₃ h₂₀ h₃₀ S.g hg) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, postcompLinear_apply]
  constructor
  · rintro ⟨y, rfl⟩
    simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, S.zero, mk₀_zero, comp_zero]
  · exact fun hx => covariant_sequence_exact₂ A hS x hx

omit [Module R (Ext A S.X₁ n₀)] [Module R (Ext A S.X₂ n₁)] in
/-- Exactness of the long exact sequence at `Ext^n(A, S.X₃)`. -/
theorem range_postcompLinear_g_eq_ker_extClassLinear :
    LinearMap.range (postcompLinear μ₂ μ₃ h₂₀ h₃₀ S.g hg) =
      LinearMap.ker (extClassLinear hS h μ₁ μ₂ μ₃ h₃₀ h₁₁ hf hg) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, postcompLinear_apply, extClassLinear_apply]
  constructor
  · rintro ⟨y, rfl⟩
    simp only [comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, comp_zero]
  · exact fun hx => covariant_sequence_exact₃ A hS x h hx

omit [Module R (Ext A S.X₁ n₀)] [Module R (Ext A S.X₂ n₀)] in
/-- Exactness of the long exact sequence at `Ext^{n+1}(A, S.X₁)`. -/
theorem range_extClassLinear_eq_ker_postcompLinear_f :
    LinearMap.range (extClassLinear hS h μ₁ μ₂ μ₃ h₃₀ h₁₁ hf hg) =
      LinearMap.ker (postcompLinear μ₁ μ₂ h₁₁ h₂₁ S.f hf) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, postcompLinear_apply, extClassLinear_apply]
  constructor
  · rintro ⟨y, rfl⟩
    simp only [comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp, comp_zero]
  · exact fun hx => covariant_sequence_exact₁ A hS x hx h

end Exact

end CategoryTheory.Abelian.Ext

end
