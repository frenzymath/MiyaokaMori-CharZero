import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.WeightDecompositionAppLE

/-! # Coassociativity of a `G_m`-action on sections

`GroupSchemeAction.exists_coassoc_appLE` is the associativity axiom `mul_act` of a `G_m`-action
`α : G_m ×_k T → T`, read on sections. Write `W := G_m ×_k T`, `V_W := pr₂⁻¹V` and
`W₂ := G_m ×_k W` (fibre product along `pr₂ ≫ q`), and consider the two morphisms `W₂ → W`
given by `m_W = (g,(h,t)) ↦ (gh, t)` and `a_W = (g,(h,t)) ↦ (g, h·t)`. The axiom `mul_act` says
`m_W ≫ act = a_W ≫ act` (via the associativity morphism `j : W₂ → (G_m ×_k G_m) ×_k T`); taking
sections over `V_W` gives the coassociativity of the coaction.

* `Gm.mulHom_appTop_lambda`: `μ^♯(λ) = pr₁^♯(λ) · pr₂^♯(λ)` in `Γ(G_m ×_k G_m)` (the Hopf algebra
  comultiplication `comul_T`).
* `exists_coassoc_appLE`: the coassociativity statement used by `WeightDecomposition.lean`.

References: Stacks Project, Tag 0EKK (coassociativity); Mathlib's `mul_spec_asOver_spec_left`,
`LaurentPolynomial.comul_T` and `pullbackSpecIso_hom_fst/snd`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct CategoryTheory.MonoidalCategory

noncomputable section

namespace GroupSchemeAction

/-! ## The multiplication of `G_m` on `λ`: `μ^♯(λ) = pr₁^♯(λ) · pr₂^♯(λ)` -/

section MulLambda

variable (k : Type u) [Field k]

/-- The multiplication `μ = (MonObj.mul).left : G_m ×_k G_m → G_m` of `G_m`; by
`mul_spec_asOver_spec_left`, `μ = pullbackSpecIso.hom ≫ Spec (comul)`. It is typed as
`pullback 𝔤 𝔤 ⟶ Gm k`. -/
def Gm.mulHom :
    CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ⟶
      ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).left :=
  (CategoryTheory.MonObj.mul : (Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ⊗
      (Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟶
    (Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).left

theorem Gm.mulHom_eq :
    Gm.mulHom k = (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (LaurentPolynomial k)).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k (LaurentPolynomial k))) :=
  rfl

/-- **`μ^♯(λ) = pr₁^♯(λ) · pr₂^♯(λ)`** in `Γ(G_m ×_k G_m, ⊤)`.
Proof: `μ = pullbackSpecIso.hom ≫ Spec(Δ)` and `Δ(T 1) = T 1 ⊗ T 1 = (T 1 ⊗ 1)(1 ⊗ T 1)`
(`comul_T`, `tmul_mul_tmul`); naturality of `ΓSpecIso` rewrites `Spec(Δ)^♯(ΓSpecIso⁻¹ (T 1))` as
`ΓSpecIso⁻¹(T 1 ⊗ T 1)`, and `pullbackSpecIso_hom_fst/snd` replace
`pullbackSpecIso.hom ≫ Spec(inclL/inclR)` by `pr₁` / `pr₂`. -/
theorem Gm.mulHom_appTop_lambda :
    ((Gm.mulHom k).appTop).hom (Gm.lambda k) =
      ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom).appTop).hom (Gm.lambda k) *
      ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom).appTop).hom (Gm.lambda k) := by
  -- Δ(T 1) = (T 1 ⊗ 1) * (1 ⊗ T 1)
  have hΔ : (CommRingCat.ofHom (Bialgebra.comulAlgHom k (LaurentPolynomial k) :
        LaurentPolynomial k →+* LaurentPolynomial k ⊗[k] LaurentPolynomial k)).hom (LaurentPolynomial.T 1) =
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          LaurentPolynomial k →+* LaurentPolynomial k ⊗[k] LaurentPolynomial k)).hom (LaurentPolynomial.T 1) *
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          LaurentPolynomial k →ₐ[k] LaurentPolynomial k ⊗[k] LaurentPolynomial k).toRingHom).hom
          (LaurentPolynomial.T 1) := by
    show Bialgebra.comulAlgHom k (LaurentPolynomial k) (LaurentPolynomial.T 1) =
      Algebra.TensorProduct.includeLeftRingHom (LaurentPolynomial.T 1) *
        Algebra.TensorProduct.includeRight (LaurentPolynomial.T 1)
    rw [Bialgebra.comulAlgHom_apply, LaurentPolynomial.comul_T,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  -- pr₁ = P.hom ≫ Spec inclL, pr₂ = P.hom ≫ Spec inclR
  have hfst := AlgebraicGeometry.pullbackSpecIso_hom_fst k (LaurentPolynomial k) (LaurentPolynomial k)
  have hsnd := AlgebraicGeometry.pullbackSpecIso_hom_snd k (LaurentPolynomial k) (LaurentPolynomial k)
  -- elementwise; everything is stated on the Spec side and moved to G_m by definitional unfolding at the end
  have e2 : ∀ (f : CommRingCat.of (LaurentPolynomial k) ⟶
        CommRingCat.of (LaurentPolynomial k ⊗[k] LaurentPolynomial k))
      (g : _ ⟶ AlgebraicGeometry.Spec (CommRingCat.of (LaurentPolynomial k))),
      (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (LaurentPolynomial k)).hom ≫
        AlgebraicGeometry.Spec.map f = g →
      ((AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (LaurentPolynomial k)).hom.appTop).hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (LaurentPolynomial k ⊗[k] LaurentPolynomial k))).inv.hom
          (f.hom (LaurentPolynomial.T 1))) =
        (g.appTop).hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1)) := by
    intro f g hg
    rw [← Gm.Spec_map_appTop_ΓSpecIso_inv, ← hg, AlgebraicGeometry.Scheme.Hom.comp_appTop]
    rfl
  have hL := e2 _ _ hfst
  have hR := e2 _ _ hsnd
  have e1 : (((AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (LaurentPolynomial k)).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k (LaurentPolynomial k) :
          LaurentPolynomial k →+* LaurentPolynomial k ⊗[k] LaurentPolynomial k))).appTop).hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1)) =
      ((AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (LaurentPolynomial k)).hom.appTop).hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (LaurentPolynomial k ⊗[k] LaurentPolynomial k))).inv.hom
        ((CommRingCat.ofHom (Bialgebra.comulAlgHom k (LaurentPolynomial k) :
          LaurentPolynomial k →+* LaurentPolynomial k ⊗[k] LaurentPolynomial k)).hom
            (LaurentPolynomial.T 1))) := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_appTop]
    show ((AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (LaurentPolynomial k)).hom.appTop).hom
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k (LaurentPolynomial k) :
          LaurentPolynomial k →+* LaurentPolynomial k ⊗[k] LaurentPolynomial k))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1))) = _
    rw [Gm.Spec_map_appTop_ΓSpecIso_inv]
  rw [hΔ, map_mul, map_mul] at e1
  exact e1.trans (congrArg₂ (· * ·) hL hR)

end MulLambda

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}

/-! ## Local notation (expanded textually, so the variable names must be `k`, `S`, `T`, `U`; the same as in `WeightDecomposition.lean`) -/

set_option quotPrecheck false
set_option hygiene false

/-- Spec k -/
local notation "Specₖ" => AlgebraicGeometry.Spec (CommRingCat.of k)
/-- G_m → Spec k -/
local notation "𝔤" => ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
/-- q := π ≫ (S ↘ Spec k) : T → Spec k -/
local notation "𝔮" => (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
/-- pr₂ : W = G_m ×_k T → T -/
local notation "𝔭𝔯₂" => CategoryTheory.Limits.pullback.snd
  ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
  (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
/-- pr₁ : W = G_m ×_k T → G_m -/
local notation "𝔭𝔯₁" => CategoryTheory.Limits.pullback.fst
  ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
  (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
/-- V := π⁻¹U -/
local notation "𝔙" => (T.hom ⁻¹ᵁ U)
/-- pr₂' : W₂ = G_m ×_k W → W -/
local notation "𝔭𝔯₂'" => CategoryTheory.Limits.pullback.snd
  ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
  (CategoryTheory.Limits.pullback.snd
    ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
/-- pr₁' : W₂ = G_m ×_k W → G_m -/
local notation "𝔭𝔯₁'" => CategoryTheory.Limits.pullback.fst
  ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
  (CategoryTheory.Limits.pullback.snd
    ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))

/-! ## The two morphisms `m_W, a_W : W₂ → W` and associativity -/

/-- Compatibility condition for `inner := (pr₁', pr₂' ≫ pr₁) : W₂ → G_m ×_k G_m`. -/
theorem coassoc_inner_cond :
    𝔭𝔯₁' ≫ 𝔤 = (𝔭𝔯₂' ≫ 𝔭𝔯₁) ≫ 𝔤 := by
  simp only [CategoryTheory.Category.assoc]
  rw [CategoryTheory.Limits.pullback.condition (f := 𝔤) (g := 𝔮)]
  exact CategoryTheory.Limits.pullback.condition

/-- The morphism `inner := (pr₁', pr₂' ≫ pr₁) : W₂ → G_m ×_k G_m`. -/
def coassocInner :
    CategoryTheory.Limits.pullback 𝔤 (𝔭𝔯₂ ≫ 𝔮) ⟶ CategoryTheory.Limits.pullback 𝔤 𝔤 :=
  CategoryTheory.Limits.pullback.lift 𝔭𝔯₁' (𝔭𝔯₂' ≫ 𝔭𝔯₁) coassoc_inner_cond

/-- `μ ≫ 𝔤 = pr₁ ≫ 𝔤` (from `mulAct_cond₁`). -/
theorem mulHom_comp_hom :
    Gm.mulHom k ≫ 𝔤 = CategoryTheory.Limits.pullback.fst 𝔤 𝔤 ≫ 𝔤 := by
  have h := GroupSchemeAction.mulAct_cond₁ ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
  rw [CategoryTheory.Category.comp_id] at h
  exact h.symm

/-- Compatibility condition for `m_W := (inner ≫ μ, pr₂' ≫ pr₂)`. -/
theorem coassoc_mul_cond :
    (coassocInner (k := k) (S := S) (T := T) ≫ Gm.mulHom k) ≫ 𝔤 = (𝔭𝔯₂' ≫ 𝔭𝔯₂) ≫ 𝔮 := by
  simp only [CategoryTheory.Category.assoc]
  rw [mulHom_comp_hom, coassocInner, CategoryTheory.Limits.pullback.lift_fst_assoc]
  exact CategoryTheory.Limits.pullback.condition

/-- The morphism `m_W : W₂ → W`, `(g,(h,t)) ↦ (gh, t)`. -/
def coassocMul : CategoryTheory.Limits.pullback 𝔤 (𝔭𝔯₂ ≫ 𝔮) ⟶ CategoryTheory.Limits.pullback 𝔤 𝔮 :=
  CategoryTheory.Limits.pullback.lift (coassocInner ≫ Gm.mulHom k) (𝔭𝔯₂' ≫ 𝔭𝔯₂) coassoc_mul_cond

/-- Compatibility condition for `a_W := (pr₁', pr₂' ≫ act)`. -/
theorem coassoc_act_cond (α : GmActionOver k T) :
    𝔭𝔯₁' ≫ 𝔤 = (𝔭𝔯₂' ≫ α.act) ≫ 𝔮 := by
  simp only [CategoryTheory.Category.assoc]
  rw [act_comp_structure_eq α]
  exact CategoryTheory.Limits.pullback.condition

/-- The morphism `a_W : W₂ → W`, `(g,(h,t)) ↦ (g, h·t)`. -/
def coassocAct (α : GmActionOver k T) :
    CategoryTheory.Limits.pullback 𝔤 (𝔭𝔯₂ ≫ 𝔮) ⟶ CategoryTheory.Limits.pullback 𝔤 𝔮 :=
  CategoryTheory.Limits.pullback.lift 𝔭𝔯₁' (𝔭𝔯₂' ≫ α.act) (coassoc_act_cond α)

/-- Compatibility condition for the associativity morphism `j := (inner, pr₂' ≫ pr₂) : W₂ → (G_m ×_k G_m) ×_k T`. -/
theorem coassoc_assoc_cond :
    coassocInner (k := k) (S := S) (T := T) ≫ (CategoryTheory.Limits.pullback.fst 𝔤 𝔤 ≫ 𝔤) =
      (𝔭𝔯₂' ≫ 𝔭𝔯₂) ≫ 𝔮 := by
  simp only [CategoryTheory.Category.assoc]
  rw [coassocInner, CategoryTheory.Limits.pullback.lift_fst_assoc]
  exact CategoryTheory.Limits.pullback.condition

/-- The associativity morphism `j := (inner, pr₂' ≫ pr₂) : W₂ → (G_m ×_k G_m) ×_k T` (into the fibre product on which `mul_act` is stated). -/
def coassocAssoc :
    CategoryTheory.Limits.pullback 𝔤 (𝔭𝔯₂ ≫ 𝔮) ⟶
      CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.fst 𝔤 𝔤 ≫ 𝔤) 𝔮 :=
  CategoryTheory.Limits.pullback.lift coassocInner (𝔭𝔯₂' ≫ 𝔭𝔯₂) coassoc_assoc_cond

/-- **Associativity pulled back to `W₂`**: `m_W ≫ act = a_W ≫ act`.
Proof: `j ≫ (μ ×_k 𝟙) = m_W` and `j ≫ lift(fst ≫ fst, lift(fst ≫ snd, snd) ≫ act) = a_W`
(`pullback.hom_ext`, componentwise), then substitute `α.mul_act`. -/
theorem coassocMul_comp_act (α : GmActionOver k T) :
    coassocMul ≫ α.act = coassocAct α ≫ α.act := by
  have hL : coassocAssoc (k := k) (S := S) (T := T) ≫
      CategoryTheory.Limits.pullback.map (CategoryTheory.Limits.pullback.fst 𝔤 𝔤 ≫ 𝔤) 𝔮 𝔤 𝔮
        (Gm.mulHom k) (CategoryTheory.CategoryStruct.id T.left)
        (CategoryTheory.CategoryStruct.id Specₖ)
        (GroupSchemeAction.mulAct_cond₁ ((Gm k).asOver Specₖ)) (GroupSchemeAction.mulAct_cond₂ T) =
      coassocMul := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
        coassocAssoc, CategoryTheory.Limits.pullback.lift_fst_assoc,
        coassocMul, CategoryTheory.Limits.pullback.lift_fst]
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd,
        CategoryTheory.Category.comp_id, coassocAssoc, CategoryTheory.Limits.pullback.lift_snd,
        coassocMul, CategoryTheory.Limits.pullback.lift_snd]
  have hInner : coassocAssoc (k := k) (S := S) (T := T) ≫
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst _ _ ≫ CategoryTheory.Limits.pullback.snd _ _)
        (CategoryTheory.Limits.pullback.snd _ _)
        (GroupSchemeAction.mulAct_cond₃ ((Gm k).asOver Specₖ) T) = 𝔭𝔯₂' := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
        coassocAssoc, CategoryTheory.Limits.pullback.lift_fst_assoc,
        coassocInner, CategoryTheory.Limits.pullback.lift_snd]
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd,
        coassocAssoc, CategoryTheory.Limits.pullback.lift_snd]
  have hR : coassocAssoc (k := k) (S := S) (T := T) ≫
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst _ _ ≫ CategoryTheory.Limits.pullback.fst _ _)
        (CategoryTheory.Limits.pullback.lift
            (CategoryTheory.Limits.pullback.fst _ _ ≫ CategoryTheory.Limits.pullback.snd _ _)
            (CategoryTheory.Limits.pullback.snd _ _)
            (GroupSchemeAction.mulAct_cond₃ ((Gm k).asOver Specₖ) T) ≫ α.act)
        (GroupSchemeAction.mulAct_cond₄ ((Gm k).asOver Specₖ) T α.act α.act_over) =
      coassocAct α := by
    have hInner' := congrArg (fun m => m ≫ α.act) hInner
    rw [CategoryTheory.Category.assoc] at hInner'
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
        coassocAssoc, CategoryTheory.Limits.pullback.lift_fst_assoc,
        coassocInner, CategoryTheory.Limits.pullback.lift_fst,
        coassocAct, CategoryTheory.Limits.pullback.lift_fst]
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd,
        hInner', coassocAct, CategoryTheory.Limits.pullback.lift_snd]
  have h := α.mul_act
  rw [← hL, ← hR, CategoryTheory.Category.assoc, CategoryTheory.Category.assoc]
  exact congrArg (fun m => coassocAssoc ≫ m) h

/-! ## Coassociativity on sections -/

/-- **Coassociativity.** Write `W := G_m ×_k T`, `V_W := pr₂⁻¹V`, `W₂ := G_m ×_k W` (along `pr₂ ≫ q`),
`pr₂' : W₂ → W`, `V_{W₂} := pr₂'⁻¹V_W`, `ψ := pr₂'^♯ : Γ(W, V_W) → Γ(W₂, V_{W₂})`, and
`λ₁ := Gm.lambdaOn (pr₂ ≫ q) V_W` (the first coordinate of `W₂`).
There are ring homomorphisms `m, a₂ : Γ(W, V_W) → Γ(W₂, V_{W₂})` with
`m ∘ pr₂^♯ = ψ ∘ pr₂^♯`, `m(λ) = λ₁ · ψ(λ)`, `a₂ ∘ pr₂^♯ = ψ ∘ act^♯`, `a₂(λ) = λ₁`, and
**`m ∘ act^♯ = a₂ ∘ act^♯`**. (On a chart, `m = Δ ⊗ id` and `a₂ = id ⊗ co`, and the last identity is
the coassociativity of the coaction.)

References: Stacks Project, Tag 0EKK (coassociativity `(Δ ⊗ id) ∘ co = (id ⊗ co) ∘ co`); Mathlib's
`AlgebraicGeometry.mul_spec_asOver_spec_left` (`(MonObj.mul).left` of `G_m` equals
`pullbackSpecIso.hom ≫ Spec.map (comulAlgHom)`), `LaurentPolynomial.comul_T`,
`pullbackSpecIso_hom_fst/snd`.

Proof.
1. Two morphisms `W₂ → W`: `m_W := coassocMul = lift(lift(pr₁', pr₂' ≫ pr₁) ≫ μ, pr₂' ≫ pr₂)`
   (`(g,(h,t)) ↦ (gh, t)`) and `a_W := coassocAct = lift(pr₁', pr₂' ≫ act)` (`(g,(h,t)) ↦ (g, act(h,t))`).
   Since `m_W ≫ pr₂ = pr₂' ≫ pr₂`, we get `m_W⁻¹V_W = V_{W₂}`; since `a_W ≫ pr₂ = pr₂' ≫ act` and
   `act⁻¹V = pr₂⁻¹V` (`snd_comp_preimage_eq_act_preimage`), we get `a_W⁻¹V_W = V_{W₂}`.
   Put `m := m_W.appLE V_W V_{W₂}` and `a₂ := a_W.appLE V_W V_{W₂}`.
2. The identities on generators are `appLE_comp_appLE` together with `pullback.lift_fst/snd`:
   `m ∘ pr₂^♯ = (m_W ≫ pr₂)^♯ = (pr₂' ≫ pr₂)^♯ = ψ ∘ pr₂^♯`;
   `a₂ ∘ pr₂^♯ = (a_W ≫ pr₂)^♯ = (pr₂' ≫ act)^♯ = ψ ∘ act^♯`;
   `a₂(λ) = (a_W ≫ pr₁)^♯(λ_Gm) = pr₁'^♯(λ_Gm) = λ₁`.
3. `m(λ) = λ₁ · ψ(λ)`: `m_W ≫ pr₁ = inner ≫ μ` and `μ^♯(λ_Gm) = fst^♯(λ_Gm) · snd^♯(λ_Gm)`
   (`Gm.mulHom_appTop_lambda`); pulling back along `inner`, `inner ≫ fst = pr₁'` gives `λ₁` and
   `inner ≫ snd = pr₂' ≫ pr₁` gives `ψ(λ)`.
4. Coassociativity `m_W ≫ act = a_W ≫ act` (`coassocMul_comp_act`, i.e. `α.mul_act` transported along
   the associativity morphism `j`); taking sections gives `m ∘ act^♯ = a₂ ∘ act^♯`.
When `U = ∅` all the rings are zero and the statement is trivial. -/
theorem exists_coassoc_appLE (α : GmActionOver k T) (U : S.Opens) :
    ∃ m a₂ : Γ(CategoryTheory.Limits.pullback 𝔤 𝔮, 𝔭𝔯₂ ⁻¹ᵁ 𝔙) →+*
        Γ(CategoryTheory.Limits.pullback 𝔤 (𝔭𝔯₂ ≫ 𝔮),
          CategoryTheory.Limits.pullback.snd 𝔤 (𝔭𝔯₂ ≫ 𝔮) ⁻¹ᵁ (𝔭𝔯₂ ⁻¹ᵁ 𝔙)),
      (∀ a, m (((𝔭𝔯₂).appLE 𝔙 _ le_rfl).hom a) =
        ((CategoryTheory.Limits.pullback.snd 𝔤 (𝔭𝔯₂ ≫ 𝔮)).appLE (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ le_rfl).hom
          (((𝔭𝔯₂).appLE 𝔙 _ le_rfl).hom a)) ∧
      m (Gm.lambdaOn 𝔮 𝔙) = Gm.lambdaOn (𝔭𝔯₂ ≫ 𝔮) (𝔭𝔯₂ ⁻¹ᵁ 𝔙) *
        ((CategoryTheory.Limits.pullback.snd 𝔤 (𝔭𝔯₂ ≫ 𝔮)).appLE (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ le_rfl).hom
          (Gm.lambdaOn 𝔮 𝔙) ∧
      (∀ a, a₂ (((𝔭𝔯₂).appLE 𝔙 _ le_rfl).hom a) =
        ((CategoryTheory.Limits.pullback.snd 𝔤 (𝔭𝔯₂ ≫ 𝔮)).appLE (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ le_rfl).hom
          ((α.act.appLE 𝔙 _ (snd_comp_preimage_eq_act_preimage α U).le).hom a)) ∧
      a₂ (Gm.lambdaOn 𝔮 𝔙) = Gm.lambdaOn (𝔭𝔯₂ ≫ 𝔮) (𝔭𝔯₂ ⁻¹ᵁ 𝔙) ∧
      ∀ a, m ((α.act.appLE 𝔙 _ (snd_comp_preimage_eq_act_preimage α U).le).hom a) =
        a₂ ((α.act.appLE 𝔙 _ (snd_comp_preimage_eq_act_preimage α U).le).hom a) := by
  -- notation
  have hle := (snd_comp_preimage_eq_act_preimage α U).le
  have hm_snd : coassocMul (k := k) (S := S) (T := T) ≫ 𝔭𝔯₂ = 𝔭𝔯₂' ≫ 𝔭𝔯₂ :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hm_fst : coassocMul (k := k) (S := S) (T := T) ≫ 𝔭𝔯₁ = coassocInner ≫ Gm.mulHom k :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have ha_snd : coassocAct α ≫ 𝔭𝔯₂ = 𝔭𝔯₂' ≫ α.act :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  have ha_fst : coassocAct α ≫ 𝔭𝔯₁ = 𝔭𝔯₁' :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hi_fst : coassocInner (k := k) (S := S) (T := T) ≫ CategoryTheory.Limits.pullback.fst 𝔤 𝔤 = 𝔭𝔯₁' :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hi_snd : coassocInner (k := k) (S := S) (T := T) ≫ CategoryTheory.Limits.pullback.snd 𝔤 𝔤 =
      𝔭𝔯₂' ≫ 𝔭𝔯₁ :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hle_m : 𝔭𝔯₂' ⁻¹ᵁ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) ≤ coassocMul ⁻¹ᵁ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) :=
    (congrArg (fun f => f ⁻¹ᵁ 𝔙) hm_snd).symm.le
  have hle_a : 𝔭𝔯₂' ⁻¹ᵁ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) ≤ coassocAct α ⁻¹ᵁ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) := by
    have e1 := congrArg (fun f => f ⁻¹ᵁ 𝔙) ha_snd
    have e2 := congrArg (fun O => 𝔭𝔯₂' ⁻¹ᵁ O) (snd_comp_preimage_eq_act_preimage α U)
    exact (e2.trans e1.symm).le
  refine ⟨(coassocMul.appLE (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ hle_m).hom, ((coassocAct α).appLE (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ hle_a).hom,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- m ∘ pr₂^♯ = ψ ∘ pr₂^♯
    intro a
    rw [appLE_comp_appLE_apply coassocMul 𝔭𝔯₂ 𝔙 (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ le_rfl hle_m a,
      appLE_comp_appLE_apply 𝔭𝔯₂' 𝔭𝔯₂ 𝔙 (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ le_rfl le_rfl a]
    exact appLE_congr_apply hm_snd 𝔙 _ _ _ a
  · -- m(λ) = λ₁ · ψ(λ): reduce everything to appTop on Γ(W₂, ⊤), then restrict
    rw [lambdaOn_eq_appLE 𝔮 𝔙, lambdaOn_eq_appLE (𝔭𝔯₂ ≫ 𝔮) (𝔭𝔯₂ ⁻¹ᵁ 𝔙),
      appLE_comp_appLE_apply coassocMul 𝔭𝔯₁ ⊤ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ (le_preimage_top _ _) hle_m (Gm.lambda k),
      appLE_comp_appLE_apply 𝔭𝔯₂' 𝔭𝔯₁ ⊤ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ (le_preimage_top _ _) le_rfl (Gm.lambda k),
      appLE_congr_apply hm_fst ⊤ _ _ (le_preimage_top _ _) (Gm.lambda k),
      appLE_congr_apply hi_fst.symm ⊤ _ (le_preimage_top _ _) (le_preimage_top _ _) (Gm.lambda k),
      appLE_congr_apply hi_snd.symm ⊤ _ _ (le_preimage_top _ _) (Gm.lambda k),
      appLE_top_apply (coassocInner ≫ Gm.mulHom k) _ _ (Gm.lambda k),
      appLE_top_apply (coassocInner ≫ CategoryTheory.Limits.pullback.fst 𝔤 𝔤) _ _ (Gm.lambda k),
      appLE_top_apply (coassocInner ≫ CategoryTheory.Limits.pullback.snd 𝔤 𝔤) _ _ (Gm.lambda k),
      comp_appTop_apply coassocInner (Gm.mulHom k) (Gm.lambda k),
      comp_appTop_apply coassocInner (CategoryTheory.Limits.pullback.fst 𝔤 𝔤) (Gm.lambda k),
      comp_appTop_apply coassocInner (CategoryTheory.Limits.pullback.snd 𝔤 𝔤) (Gm.lambda k),
      Gm.mulHom_appTop_lambda k, map_mul, map_mul]
  · -- a₂ ∘ pr₂^♯ = ψ ∘ act^♯
    intro a
    rw [appLE_comp_appLE_apply (coassocAct α) 𝔭𝔯₂ 𝔙 (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ le_rfl hle_a a,
      appLE_comp_appLE_apply 𝔭𝔯₂' α.act 𝔙 (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ hle le_rfl a]
    exact appLE_congr_apply ha_snd 𝔙 _ _ _ a
  · -- a₂(λ) = λ₁
    rw [lambdaOn_eq_appLE 𝔮 𝔙, lambdaOn_eq_appLE (𝔭𝔯₂ ≫ 𝔮) (𝔭𝔯₂ ⁻¹ᵁ 𝔙),
      appLE_comp_appLE_apply (coassocAct α) 𝔭𝔯₁ ⊤ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ (le_preimage_top _ _) hle_a (Gm.lambda k)]
    exact appLE_congr_apply ha_fst ⊤ _ _ _ (Gm.lambda k)
  · -- coassociativity
    intro a
    rw [appLE_comp_appLE_apply coassocMul α.act 𝔙 (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ hle hle_m a,
      appLE_comp_appLE_apply (coassocAct α) α.act 𝔙 (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _ hle hle_a a]
    exact appLE_congr_apply (coassocMul_comp_act α) 𝔙 _ _ _ a

end GroupSchemeAction

end
