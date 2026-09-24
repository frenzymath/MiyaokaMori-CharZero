import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.WeightDecompositionAppLE
import MiyaokaMori.AlgebraicGeometry.Morphisms.WeightDecompositionChart

/-! # The polynomial chart of a nonnegative `G_m`-action

`GroupSchemeAction.exists_polynomial_chart_of_act'`: let `act' : A¹ ×_k T → T` (over `S`) extend a
nonnegative `G_m`-action on `T`, let `U ⊆ S` be an affine open and `V := π⁻¹U`. Then the ring of sections
of `A¹ ×_k T` over `pr₂'⁻¹V` is `k[X] ⊗_k Γ(V)` (`SpecChart.pullback_sections_tensorEquiv` with `A = k[X]`),
and restriction along `G_m ↪ A¹` sends `pr₂'^♯`, `X`, `act'^♯` to `pr₂^♯`, `λ`, `act^♯` respectively.

This is the geometric input of the weight decomposition in `WeightDecomposition.lean`. The tools are
Mathlib's `pullbackSpecIso` / `CommRingCat.isPushout_tensorProduct` (through `SpecChart`),
`Polynomial.toLaurent_X` and `specOverSpec_over`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace GroupSchemeAction

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}

/-! ## Notation (local to this file; the notations expand textually, so the variable names must be
`k`, `S`, `T`, `U`; they agree with those of `WeightDecomposition.lean`) -/

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
/-- V := π⁻¹U -/
local notation "𝔙" => (T.hom ⁻¹ᵁ U)
/-- A¹ = Spec k[X] → Spec k -/
local notation "𝔸" => (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘
  AlgebraicGeometry.Spec (CommRingCat.of k))
/-- pr₂' : W' = A¹ ×_k T → T -/
local notation "𝔭𝔯₂'" => CategoryTheory.Limits.pullback.snd
  (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
/-- incl : G_m ↪ A¹ -/
local notation "𝔦𝔫𝔠𝔩" => AlgebraicGeometry.Spec.map
  (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom)

/-- On global sections, `G_m ↪ A¹` sends `ΓSpecIso⁻¹(X)` to `λ_{G_m} = ΓSpecIso⁻¹(T 1)` (`toLaurent_X`). -/
theorem incl_appTop_X :
    ((𝔦𝔫𝔠𝔩 : Gm k ⟶ AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k))).appTop).hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X) =
      Gm.lambda k := by
  have h := Gm.Spec_map_appTop_ΓSpecIso_inv (R := CommRingCat.of (Polynomial k))
    (S := CommRingCat.of (LaurentPolynomial k))
    (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom) Polynomial.X
  have hX : (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom).hom Polynomial.X =
      LaurentPolynomial.T 1 := by
    show Polynomial.toLaurentAlg (R := k) Polynomial.X = LaurentPolynomial.T 1
    rw [Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X]
  rw [hX] at h
  exact h

/-- **The polynomial chart of a nonnegative action.** Let `act' : W' := A¹ ×_k T → T` extend `act` and lie
over `S` (`IsNonnegative.exists_act'_over`). Write `pr₂' : W' → T`, `V_{W'} := pr₂'⁻¹V` and
`j := incl ×_k 𝟙 : W → W'`, where `incl = Spec.map toLaurentAlg : G_m ↪ A¹`. Then there are ring
homomorphisms `φ', actS' : Γ(T, V) → Γ(W', V_{W'})`, an element `lam' ∈ Γ(W', V_{W'})`, a ring isomorphism
`e' : Γ(W', V_{W'}) ≃+* k[X] ⊗[k] Γ(T, V)` and a ring homomorphism `ι : Γ(W', V_{W'}) → Γ(W, pr₂⁻¹V)` with
`e'(φ' a) = 1 ⊗ a`, `e'(lam') = X ⊗ 1`, `ι ∘ φ' = pr₂^♯`, `ι(lam') = λ` and `ι ∘ actS' = act^♯`.

Reference: Mathlib `AlgebraicGeometry.pullbackSpecIso` (fibre products of affine schemes) and
`Polynomial.toLaurent_X`; the same technique as `Gm_pullback_sections_tensorEquiv`.

Proof.
1. `φ' := pr₂'.appLE V V_{W'}`; `actS' := act'.appLE V V_{W'}` (from `act' ≫ π = pr₂' ≫ π` we get
   `act'⁻¹V = pr₂'⁻¹V`); `lam' := res(pr₁'^♯(ΓSpecIso.inv X))`; `ι := j.appLE V_{W'} (pr₂⁻¹V)`
   (`j ≫ pr₂' = pr₂` by `pullback.lift_snd`).
2. `ι ∘ φ' = (j ≫ pr₂')^♯ = pr₂^♯`; `ι ∘ actS' = (j ≫ act')^♯ = act^♯` (the equation `hact'`);
   `ι(lam') = (j ≫ pr₁')^♯(X) = (pr₁ ≫ incl)^♯(X) = pr₁^♯(incl^♯ X) = pr₁^♯(T 1) = λ`
   (`appLE_comp_appLE`, `appLE_hom_congr_of_eq`, `incl_appTop_X`).
3. `e'`: `SpecChart.pullback_sections_tensorEquiv` (`WeightDecompositionChart.lean`, the general form of the
   `G_m` chart) with `A = k[X]` and `f = (A¹ ↘ Spec k) = Spec (algebraMap)` (`specOverSpec_over`).
Boundary case: for `U = ∅` all rings are zero. -/
theorem exists_polynomial_chart_of_act' (α : GmActionOver k T) (U : S.Opens)
    (hV : AlgebraicGeometry.IsAffineOpen (T.hom ⁻¹ᵁ U))
    (act' : CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        𝔮 ⟶ T.left)
    (hact' : CategoryTheory.Limits.pullback.map _ _ _ _
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom))
          (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _)
          GroupSchemeAction.isNonnegative_cond₁ (GroupSchemeAction.isNonnegative_cond₂ T) ≫ act' =
        α.act)
    (hover : act' ≫ T.hom = CategoryTheory.Limits.pullback.snd _ _ ≫ T.hom) :
    letI := Gm.sectionsAlgebra 𝔮 𝔙
    ∃ (φ' actS' : Γ(T.left, 𝔙) →+*
          Γ(CategoryTheory.Limits.pullback
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮,
            CategoryTheory.Limits.pullback.snd
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮
              ⁻¹ᵁ 𝔙))
      (lam' : Γ(CategoryTheory.Limits.pullback
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮,
            CategoryTheory.Limits.pullback.snd
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮
              ⁻¹ᵁ 𝔙))
      (e' : Γ(CategoryTheory.Limits.pullback
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮,
            CategoryTheory.Limits.pullback.snd
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮
              ⁻¹ᵁ 𝔙) ≃+* (Polynomial k ⊗[k] Γ(T.left, 𝔙)))
      (ι : Γ(CategoryTheory.Limits.pullback
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮,
            CategoryTheory.Limits.pullback.snd
              (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝔮
              ⁻¹ᵁ 𝔙) →+* Γ(CategoryTheory.Limits.pullback 𝔤 𝔮, 𝔭𝔯₂ ⁻¹ᵁ 𝔙)),
      (∀ a, e' (φ' a) = (1 : Polynomial k) ⊗ₜ[k] a) ∧
      e' lam' = (Polynomial.X : Polynomial k) ⊗ₜ[k] (1 : Γ(T.left, 𝔙)) ∧
      (∀ a, ι (φ' a) = ((𝔭𝔯₂).appLE 𝔙 _ le_rfl).hom a) ∧
      ι lam' = Gm.lambdaOn 𝔮 𝔙 ∧
      ∀ a, ι (actS' a) = (α.act.appLE 𝔙 _ (snd_comp_preimage_eq_act_preimage α U).le).hom a := by
  letI := Gm.sectionsAlgebra 𝔮 𝔙
  have hA : 𝔸 = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) :=
    AlgebraicGeometry.specOverSpec_over ..
  -- 3. The chart.
  obtain ⟨e', he'_φ, he'_x⟩ := SpecChart.pullback_sections_tensorEquiv 𝔸 𝔮 𝔙 hV hA
  -- 1. j := incl ×_k 𝟙 and its components.
  let j : CategoryTheory.Limits.pullback 𝔤 𝔮 ⟶ CategoryTheory.Limits.pullback 𝔸 𝔮 :=
    CategoryTheory.Limits.pullback.map _ _ _ _ 𝔦𝔫𝔠𝔩
      (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _)
      GroupSchemeAction.isNonnegative_cond₁ (GroupSchemeAction.isNonnegative_cond₂ T)
  have hj_snd : j ≫ 𝔭𝔯₂' = 𝔭𝔯₂ := by
    rw [CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Category.comp_id]
  have hj_fst : j ≫ CategoryTheory.Limits.pullback.fst 𝔸 𝔮 =
      CategoryTheory.Limits.pullback.fst 𝔤 𝔮 ≫ 𝔦𝔫𝔠𝔩 :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hj_act : j ≫ act' = α.act := hact'
  have hle_j : 𝔭𝔯₂ ⁻¹ᵁ 𝔙 ≤ j ⁻¹ᵁ (𝔭𝔯₂' ⁻¹ᵁ 𝔙) :=
    (congrArg (fun f => f ⁻¹ᵁ 𝔙) hj_snd).symm.le
  have hle_act' : 𝔭𝔯₂' ⁻¹ᵁ 𝔙 ≤ act' ⁻¹ᵁ 𝔙 :=
    (congrArg (fun f => f ⁻¹ᵁ U) hover).symm.le
  refine ⟨((𝔭𝔯₂').appLE 𝔙 _ le_rfl).hom, (act'.appLE 𝔙 _ hle_act').hom,
    ((CategoryTheory.Limits.pullback 𝔸 𝔮).presheaf.map (CategoryTheory.homOfLE le_top).op).hom
      ((CategoryTheory.Limits.pullback.fst 𝔸 𝔮).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X)),
    e', (j.appLE (𝔭𝔯₂' ⁻¹ᵁ 𝔙) (𝔭𝔯₂ ⁻¹ᵁ 𝔙) hle_j).hom, he'_φ, he'_x Polynomial.X, ?_, ?_, ?_⟩
  · -- ι ∘ φ' = pr₂^♯
    intro a
    have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE j 𝔭𝔯₂' 𝔙 (𝔭𝔯₂' ⁻¹ᵁ 𝔙) (𝔭𝔯₂ ⁻¹ᵁ 𝔙)
      le_rfl hle_j
    rw [appLE_hom_congr_of_eq hj_snd] at h
    have h' := congrArg (fun φ : Γ(T.left, 𝔙) ⟶ Γ(CategoryTheory.Limits.pullback 𝔤 𝔮, 𝔭𝔯₂ ⁻¹ᵁ 𝔙) =>
      φ.hom a) h
    exact h'
  · -- ι(lam') = λ
    -- First absorb the restriction into appLE: ι(res x) = j.appLE ⊤ _ x.
    have h0 := AlgebraicGeometry.Scheme.Hom.map_appLE j hle_j
      (CategoryTheory.homOfLE (le_top : 𝔭𝔯₂' ⁻¹ᵁ 𝔙 ≤ ⊤)).op
    have h0' := congrArg (fun φ : Γ(CategoryTheory.Limits.pullback 𝔸 𝔮, ⊤) ⟶
        Γ(CategoryTheory.Limits.pullback 𝔤 𝔮, 𝔭𝔯₂ ⁻¹ᵁ 𝔙) =>
      φ.hom ((CategoryTheory.Limits.pullback.fst 𝔸 𝔮).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X))) h0
    -- pr₁'^♯ ≫ j^♯ = incl^♯ ≫ pr₁^♯ (both equal (j ≫ pr₁')^♯ = (pr₁ ≫ incl)^♯; `comp_appLE`).
    have hA' := AlgebraicGeometry.Scheme.Hom.comp_appLE j (CategoryTheory.Limits.pullback.fst 𝔸 𝔮)
      ⊤ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) le_top
    have hB' := AlgebraicGeometry.Scheme.Hom.comp_appLE (CategoryTheory.Limits.pullback.fst 𝔤 𝔮)
      𝔦𝔫𝔠𝔩 ⊤ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) le_top
    have hφ := hA'.symm.trans ((appLE_hom_congr_of_eq hj_fst ⊤ (𝔭𝔯₂ ⁻¹ᵁ 𝔙) _).trans hB')
    have h1 := congrArg (fun φ : Γ(AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)), ⊤) ⟶
        Γ(CategoryTheory.Limits.pullback 𝔤 𝔮, 𝔭𝔯₂ ⁻¹ᵁ 𝔙) =>
      φ.hom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X)) hφ
    have h2 := congrArg ((CategoryTheory.Limits.pullback.fst 𝔤 𝔮).appLE (𝔦𝔫𝔠𝔩 ⁻¹ᵁ ⊤) (𝔭𝔯₂ ⁻¹ᵁ 𝔙) le_top).hom
      (incl_appTop_X (k := k))
    -- λ = pr₁.appLE ⊤ _ (λ_Gm) (the definition of `Gm.lambdaOn` unfolds to `appLE`).
    have h3 : ((CategoryTheory.Limits.pullback.fst 𝔤 𝔮).appLE (𝔦𝔫𝔠𝔩 ⁻¹ᵁ ⊤) (𝔭𝔯₂ ⁻¹ᵁ 𝔙) le_top).hom
        (Gm.lambda k) = Gm.lambdaOn 𝔮 𝔙 := rfl
    exact ((h0'.trans h1).trans h2).trans h3
  · -- ι ∘ actS' = act^♯
    intro a
    have h := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE j act' 𝔙 (𝔭𝔯₂' ⁻¹ᵁ 𝔙) (𝔭𝔯₂ ⁻¹ᵁ 𝔙)
      hle_act' hle_j
    rw [appLE_hom_congr_of_eq hj_act] at h
    have h' := congrArg (fun φ : Γ(T.left, 𝔙) ⟶ Γ(CategoryTheory.Limits.pullback 𝔤 𝔮, 𝔭𝔯₂ ⁻¹ᵁ 𝔙) =>
      φ.hom a) h
    exact h'

end GroupSchemeAction

end
