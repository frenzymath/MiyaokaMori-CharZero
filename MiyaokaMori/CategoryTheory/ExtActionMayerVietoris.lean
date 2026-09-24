import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopLinear
import MiyaokaMori.RingTheory.Localization.Stacks01xkLocalizationFiveLemma
import Mathlib.CategoryTheory.Square

/-! # Ext with a ring action, Mayer–Vietoris, and the localization five lemma

**Contravariant `Ext` with a ring action, the Mayer–Vietoris sequence in product form, and the
localization five lemma for it — all over an abstract abelian category.**

Setting: `C` abelian with `HasExt`, `F : C`, `R` a commutative ring acting on `F` by endomorphisms
`μ : R → (F ⟶ F)` (class `ExtAction R F`). Then every `Ext A F n` is an `R`-module by
`r • x = x.comp (mk₀ (μ r))` (`ExtAction.module`, the formula of `Ext.moduleOfEndHom`, used as a
*local* instance). This file provides, for this module structure:

* `precompLinear R F f n : Ext A F n →ₗ[R] Ext B F n` for `f : B ⟶ A` (precomposition with `mk₀ f`),
  functorial (`precompLinear_comp`, `precompLinear_id`);
* for a commutative square `sq : Square C` whose associated short complex
  `sq.mvShortComplex : X₁ → X₂ ⊞ X₃ → X₄` (maps `biprod.lift f₁₂ (-f₁₃)`, `biprod.desc f₂₄ f₃₄`;
  this is literally Mathlib's `MayerVietorisSquare.shortComplex` when `sq` is the image of a
  Mayer–Vietoris square under the free-sheaf functor) is short exact, the Mayer–Vietoris maps in
  product form `mvToProd`, `mvFromProd`, `mvDelta` (all `R`-linear) and their exactness
  (`mv_exact_toProd_fromProd`, `mv_exact_fromProd_delta`, `mv_exact_delta_toProd`,
  `mvToProd_zero_injective`); these are Mathlib's `Ext.contravariant_sequence_exact₁/₂/₃` and
  `Ext.precomp_mk₀_injective_of_epi` transported along `Ext.biprodAddEquiv`;
* naturality of the three maps under a morphism of squares `t : sq' → sq`
  (`mvToProd_precompLinear`, `mvFromProd_precompLinear`, `mvDelta_precompLinear`; the last is
  `ShortComplex.ShortExact.extClass_naturality` for the induced morphism `mvShortComplexHom`);
* **the induction step** `isLocalizedModule_precompLinear_of_mv`: if the vertical maps
  `precompLinear R F tᵢ n` (`i = 1, 2, 3`) are localizations at `S ⊆ R` for all `n`, so is
  `precompLinear R F t₄ n` for all `n`. Proof: the five lemma for localizations
  (`IsLocalizedModule.of_exact_ladder`) applied to the two
  Mayer–Vietoris sequences and the ladder of restriction maps; in degree `0` the sequence is
  prolonged by `0 → 0 → Ext X₄ F 0` using `mvToProd_zero_injective`, in degree `n + 1` the five
  terms are `Ext X₂ n × Ext X₃ n → Ext X₁ n → Ext X₄ (n+1) → Ext X₂ (n+1) × Ext X₃ (n+1) → Ext X₁ (n+1)`
  (products of localizations are localizations: `IsLocalizedModule.prodMap`).

Everything is proved over an abstract category for a performance reason (see also
`ExtPostcompLinear`): for the concrete instance `HasExt.standard` on sheaves the kernel
spends 3–7 s per declaration comparing instance paths on `Ext`; over an abstract category this does
not happen, and the concrete files only instantiate.

Source: Stacks 01XJ proof paragraph 2 (Mayer–Vietoris + five lemma), Stacks 01EC; Mathlib
`Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`. Used in the proof of Stacks 01XK. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe w v u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A commutative ring `R` acting on an object `F` by endomorphisms (`μ r : F ⟶ F`), compatibly
with `1`, `*`, `+`, `0`. It makes every `Ext A F n` an `R`-module (`ExtAction.module`). -/
class ExtAction (R : Type*) [CommRing R] (F : C) where
  /-- the endomorphism by which `r` acts -/
  μ : R → (F ⟶ F)
  μ_one : μ 1 = 𝟙 F
  μ_mul : ∀ r s, μ (r * s) = μ r ≫ μ s
  μ_add : ∀ r s, μ (r + s) = μ r + μ s
  μ_zero : μ 0 = 0

variable (R : Type*) [CommRing R] (F : C) [ExtAction R F]

/-- The `R`-module structure on `Ext A F n` given by an `ExtAction`: `r • x = x ∘ μ r`. -/
@[instance_reducible] def ExtAction.module (A : C) (n : ℕ) : Module R (Ext A F n) :=
  Ext.moduleOfEndHom A F (ExtAction.μ (F := F)) ExtAction.μ_one ExtAction.μ_mul ExtAction.μ_add
    ExtAction.μ_zero n

attribute [local instance] ExtAction.module

theorem ExtAction.smul_def {A : C} {n : ℕ} (r : R) (x : Ext A F n) :
    r • x = x.comp (mk₀ (ExtAction.μ r)) (add_zero n) := rfl

section Precomp

/-- Precomposition with `mk₀ f`, `Ext A F n → Ext B F n`, as an `R`-linear map. -/
def precompLinear {A B : C} (f : B ⟶ A) (n : ℕ) : Ext A F n →ₗ[R] Ext B F n where
  toFun x := (mk₀ f).comp x (zero_add n)
  map_add' x y := comp_add _ _ _ _
  map_smul' r x := by
    rw [RingHom.id_apply, ExtAction.smul_def, ExtAction.smul_def]
    exact (comp_assoc_of_third_deg_zero _ _ _ _).symm

variable {A B : C} (f : B ⟶ A) (n : ℕ)

@[simp] theorem precompLinear_apply (x : Ext A F n) :
    precompLinear R F f n x = (mk₀ f).comp x (zero_add n) := rfl

theorem precompLinear_comp {B' : C} (g : B' ⟶ B) (x : Ext A F n) :
    precompLinear R F g n (precompLinear R F f n x) = precompLinear R F (g ≫ f) n x := by
  simp only [precompLinear_apply, mk₀_comp_mk₀_assoc]

theorem precompLinear_id (x : Ext A F n) : precompLinear R F (𝟙 A) n x = x := by
  simp only [precompLinear_apply, mk₀_id_comp]

theorem precompLinear_congr {g : B ⟶ A} (h : f = g) (x : Ext A F n) :
    precompLinear R F f n x = precompLinear R F g n x := by rw [h]

end Precomp

section MayerVietoris

/-- The short complex `X₁ → X₂ ⊞ X₃ → X₄` attached to a commutative square (maps
`biprod.lift f₁₂ (-f₁₃)` and `biprod.desc f₂₄ f₃₄`; the same formula as
`GrothendieckTopology.MayerVietorisSquare.shortComplex`). -/
abbrev _root_.CategoryTheory.Square.mvShortComplex (sq : Square C) : ShortComplex C where
  X₁ := sq.X₁
  X₂ := sq.X₂ ⊞ sq.X₃
  X₃ := sq.X₄
  f := biprod.lift sq.f₁₂ (-sq.f₁₃)
  g := biprod.desc sq.f₂₄ sq.f₃₄
  zero := by
    rw [biprod.lift_desc, Preadditive.neg_comp, sq.fac, add_neg_cancel]

variable (sq : Square C)

omit [HasExt.{w} C] in
@[simp] theorem _root_.CategoryTheory.Square.mvShortComplex_X₁ : sq.mvShortComplex.X₁ = sq.X₁ := rfl
omit [HasExt.{w} C] in
@[simp] theorem _root_.CategoryTheory.Square.mvShortComplex_X₂ :
    sq.mvShortComplex.X₂ = (sq.X₂ ⊞ sq.X₃) := rfl
omit [HasExt.{w} C] in
@[simp] theorem _root_.CategoryTheory.Square.mvShortComplex_X₃ : sq.mvShortComplex.X₃ = sq.X₄ := rfl
omit [HasExt.{w} C] in
@[simp] theorem _root_.CategoryTheory.Square.mvShortComplex_f :
    sq.mvShortComplex.f = biprod.lift sq.f₁₂ (-sq.f₁₃) := rfl
omit [HasExt.{w} C] in
@[simp] theorem _root_.CategoryTheory.Square.mvShortComplex_g :
    sq.mvShortComplex.g = biprod.desc sq.f₂₄ sq.f₃₄ := rfl

/-- `Ext X₄ F n → Ext X₂ F n × Ext X₃ F n`: the two restrictions. -/
def mvToProd (n : ℕ) : Ext sq.X₄ F n →ₗ[R] Ext sq.X₂ F n × Ext sq.X₃ F n :=
  (precompLinear R F sq.f₂₄ n).prod (precompLinear R F sq.f₃₄ n)

/-- `Ext X₂ F n × Ext X₃ F n → Ext X₁ F n`: the difference of the two restrictions. -/
def mvFromProd (n : ℕ) : Ext sq.X₂ F n × Ext sq.X₃ F n →ₗ[R] Ext sq.X₁ F n :=
  (precompLinear R F sq.f₁₂ n).comp (LinearMap.fst _ _ _) -
    (precompLinear R F sq.f₁₃ n).comp (LinearMap.snd _ _ _)

theorem mvToProd_apply (n : ℕ) (x : Ext sq.X₄ F n) :
    mvToProd R F sq n x = (precompLinear R F sq.f₂₄ n x, precompLinear R F sq.f₃₄ n x) := rfl

theorem mvFromProd_apply (n : ℕ) (p : Ext sq.X₂ F n × Ext sq.X₃ F n) :
    mvFromProd R F sq n p = precompLinear R F sq.f₁₂ n p.1 - precompLinear R F sq.f₁₃ n p.2 := rfl

variable (hS : sq.mvShortComplex.ShortExact)

/-- The connecting map `Ext X₁ F n₀ → Ext X₄ F n₁` (`n₀ + 1 = n₁`): precomposition with the Ext
class of the short exact sequence. -/
def mvDelta (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Ext sq.X₁ F n₀ →ₗ[R] Ext sq.X₄ F n₁ where
  toFun x := hS.extClass.comp x (by omega)
  map_add' x y := comp_add _ _ _ _
  map_smul' r x := by
    rw [RingHom.id_apply, ExtAction.smul_def, ExtAction.smul_def]
    exact (comp_assoc_of_third_deg_zero _ _ _ _).symm

theorem mvDelta_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Ext sq.X₁ F n₀) :
    mvDelta R F sq hS n₀ n₁ h x = hS.extClass.comp x (by omega) := rfl

/-- Conversion: `biprodAddEquiv ((mk₀ g).comp x) = mvToProd x`. -/
theorem biprodAddEquiv_mk₀_g_comp (n : ℕ) (x : Ext sq.X₄ F n) :
    Ext.biprodAddEquiv ((mk₀ sq.mvShortComplex.g).comp x (zero_add n)) = mvToProd R F sq n x := by
  rw [mvToProd_apply]
  refine Prod.ext ?_ ?_
  · rw [Ext.biprodAddEquiv_apply_fst, mk₀_comp_mk₀_assoc, precompLinear_apply]
    congr 2
    exact biprod.inl_desc _ _
  · rw [Ext.biprodAddEquiv_apply_snd, mk₀_comp_mk₀_assoc, precompLinear_apply]
    congr 2
    exact biprod.inr_desc _ _

/-- Conversion: `(mk₀ f).comp (biprodAddEquiv.symm p) = mvFromProd p`. -/
theorem mk₀_f_comp_biprodAddEquiv_symm (n : ℕ) (p : Ext sq.X₂ F n × Ext sq.X₃ F n) :
    (mk₀ sq.mvShortComplex.f).comp (Ext.biprodAddEquiv.symm p) (zero_add n) =
      mvFromProd R F sq n p := by
  rw [Ext.biprodAddEquiv_symm_apply, comp_add, mk₀_comp_mk₀_assoc, mk₀_comp_mk₀_assoc,
    mvFromProd_apply, precompLinear_apply, precompLinear_apply, sub_eq_add_neg]
  congr 1
  · congr 2
    exact biprod.lift_fst _ _
  · rw [← neg_comp, ← mk₀_neg]
    congr 2
    exact biprod.lift_snd _ _

include hS in
theorem mv_exact_toProd_fromProd (n : ℕ) :
    Function.Exact (mvToProd R F sq n) (mvFromProd R F sq n) := by
  intro p
  constructor
  · intro hp
    have h1 := hp
    rw [← mk₀_f_comp_biprodAddEquiv_symm] at h1
    obtain ⟨x, hx⟩ := contravariant_sequence_exact₂ hS F _ h1
    refine ⟨x, ?_⟩
    rw [← biprodAddEquiv_mk₀_g_comp, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    rw [← mk₀_f_comp_biprodAddEquiv_symm, ← biprodAddEquiv_mk₀_g_comp, AddEquiv.symm_apply_apply,
      mk₀_comp_mk₀_assoc, sq.mvShortComplex.zero, mk₀_zero, zero_comp]

theorem mv_exact_fromProd_delta (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (mvFromProd R F sq n₀) (mvDelta R F sq hS n₀ n₁ h) := by
  intro y
  constructor
  · intro hy
    rw [mvDelta_apply] at hy
    obtain ⟨x₂, hx₂⟩ := contravariant_sequence_exact₁ hS F y (by omega) hy
    refine ⟨Ext.biprodAddEquiv x₂, ?_⟩
    rw [← mk₀_f_comp_biprodAddEquiv_symm, AddEquiv.symm_apply_apply, hx₂]
  · rintro ⟨p, rfl⟩
    rw [mvDelta_apply, ← mk₀_f_comp_biprodAddEquiv_symm,
      ← comp_assoc_of_second_deg_zero (a₁ := 1) (a₃ := n₀) (a₁₃ := n₁) _ _ _ (by omega),
      hS.extClass_comp, zero_comp]

theorem mv_exact_delta_toProd (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (mvDelta R F sq hS n₀ n₁ h) (mvToProd R F sq n₁) := by
  intro x
  constructor
  · intro hx
    rw [← biprodAddEquiv_mk₀_g_comp, map_eq_zero_iff _ Ext.biprodAddEquiv.injective] at hx
    obtain ⟨x₁, hx₁⟩ := contravariant_sequence_exact₃ hS F x hx (n₀ := n₀) (by omega)
    exact ⟨x₁, by rw [mvDelta_apply, hx₁]⟩
  · rintro ⟨y, rfl⟩
    rw [← biprodAddEquiv_mk₀_g_comp, mvDelta_apply,
      ← comp_assoc (a₁ := 0) (a₂ := 1) (a₃ := n₀) (a₁₂ := 1) (a₂₃ := n₁) (a := n₁) _ _ _ rfl (by omega)
        (by omega), hS.comp_extClass, zero_comp, map_zero]

include hS in
theorem mvToProd_zero_injective : Function.Injective (mvToProd R F sq 0) := by
  intro x y hxy
  rw [← biprodAddEquiv_mk₀_g_comp, ← biprodAddEquiv_mk₀_g_comp] at hxy
  have h := Ext.biprodAddEquiv.injective hxy
  have : Epi sq.mvShortComplex.g := hS.epi_g
  exact precomp_mk₀_injective_of_epi F sq.mvShortComplex.g h

end MayerVietoris

section Naturality

variable (sq' sq : Square C)
  (t₁ : sq'.X₁ ⟶ sq.X₁) (t₂ : sq'.X₂ ⟶ sq.X₂) (t₃ : sq'.X₃ ⟶ sq.X₃) (t₄ : sq'.X₄ ⟶ sq.X₄)
  (c₁₂ : sq'.f₁₂ ≫ t₂ = t₁ ≫ sq.f₁₂) (c₁₃ : sq'.f₁₃ ≫ t₃ = t₁ ≫ sq.f₁₃)
  (c₂₄ : sq'.f₂₄ ≫ t₄ = t₂ ≫ sq.f₂₄) (c₃₄ : sq'.f₃₄ ≫ t₄ = t₃ ≫ sq.f₃₄)

/-- The morphism of short complexes `sq'.mvShortComplex ⟶ sq.mvShortComplex` induced by a
morphism of squares. -/
def _root_.CategoryTheory.Square.mvShortComplexHom : sq'.mvShortComplex ⟶ sq.mvShortComplex where
  τ₁ := t₁
  τ₂ := biprod.map t₂ t₃
  τ₃ := t₄
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst, c₁₂]
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd,
        Preadditive.neg_comp, Preadditive.comp_neg, c₁₃]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, c₂₄]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, c₃₄]

include c₂₄ c₃₄ in
theorem mvToProd_precompLinear (n : ℕ) (x : Ext sq.X₄ F n) :
    mvToProd R F sq' n (precompLinear R F t₄ n x) =
      Prod.map (precompLinear R F t₂ n) (precompLinear R F t₃ n) (mvToProd R F sq n x) := by
  rw [mvToProd_apply, mvToProd_apply, Prod.map_apply, precompLinear_comp, precompLinear_comp,
    precompLinear_comp, precompLinear_comp, c₂₄, c₃₄]

include c₁₂ c₁₃ in
theorem mvFromProd_precompLinear (n : ℕ) (p : Ext sq.X₂ F n × Ext sq.X₃ F n) :
    mvFromProd R F sq' n (Prod.map (precompLinear R F t₂ n) (precompLinear R F t₃ n) p) =
      precompLinear R F t₁ n (mvFromProd R F sq n p) := by
  rw [mvFromProd_apply, mvFromProd_apply, Prod.map_apply, map_sub, precompLinear_comp,
    precompLinear_comp, precompLinear_comp, precompLinear_comp, c₁₂, c₁₃]

include t₂ t₃ c₁₂ c₁₃ c₂₄ c₃₄ in
theorem mvDelta_precompLinear (hS' : sq'.mvShortComplex.ShortExact) (hS : sq.mvShortComplex.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Ext sq.X₁ F n₀) :
    mvDelta R F sq' hS' n₀ n₁ h (precompLinear R F t₁ n₀ x) =
      precompLinear R F t₄ n₁ (mvDelta R F sq hS n₀ n₁ h x) := by
  have nat := ShortComplex.ShortExact.extClass_naturality hS' hS
    (sq'.mvShortComplexHom sq t₁ t₂ t₃ t₄ c₁₂ c₁₃ c₂₄ c₃₄)
  rw [mvDelta_apply, mvDelta_apply, precompLinear_apply, precompLinear_apply,
    ← comp_assoc_of_second_deg_zero (a₁ := 1) (a₃ := n₀) (a₁₃ := n₁) _ _ _ (by omega)]
  have e1 : (sq'.mvShortComplexHom sq t₁ t₂ t₃ t₄ c₁₂ c₁₃ c₂₄ c₃₄).τ₁ = t₁ := rfl
  have e3 : (sq'.mvShortComplexHom sq t₁ t₂ t₃ t₄ c₁₂ c₁₃ c₂₄ c₃₄).τ₃ = t₄ := rfl
  rw [e1, e3] at nat
  rw [nat, comp_assoc (a₁ := 0) (a₂ := 1) (a₃ := n₀) (a₁₂ := 1) (a₂₃ := n₁) (a := n₁) _ _ _ rfl (by omega)
    (by omega)]

end Naturality

section Induction

variable (S : Submonoid R) (sq' sq : Square C)
  (hS' : sq'.mvShortComplex.ShortExact) (hS : sq.mvShortComplex.ShortExact)
  (t₁ : sq'.X₁ ⟶ sq.X₁) (t₂ : sq'.X₂ ⟶ sq.X₂) (t₃ : sq'.X₃ ⟶ sq.X₃) (t₄ : sq'.X₄ ⟶ sq.X₄)
  (c₁₂ : sq'.f₁₂ ≫ t₂ = t₁ ≫ sq.f₁₂) (c₁₃ : sq'.f₁₃ ≫ t₃ = t₁ ≫ sq.f₁₃)
  (c₂₄ : sq'.f₂₄ ≫ t₄ = t₂ ≫ sq.f₂₄) (c₃₄ : sq'.f₃₄ ≫ t₄ = t₃ ≫ sq.f₃₄)

include hS' hS c₁₂ c₁₃ c₂₄ c₃₄ in
/-- **Mayer–Vietoris induction step for localization** (Stacks 01XJ, proof paragraph 2, in the
form used for Stacks 01XK): if the restriction maps `Ext Xᵢ F n → Ext X'ᵢ F n`
(`i = 1, 2, 3`) are localizations at `S` in every degree, so are the restriction maps
`Ext X₄ F n → Ext X'₄ F n`. -/
theorem isLocalizedModule_precompLinear_of_mv
    (h₁ : ∀ n, IsLocalizedModule S (precompLinear R F t₁ n))
    (h₂ : ∀ n, IsLocalizedModule S (precompLinear R F t₂ n))
    (h₃ : ∀ n, IsLocalizedModule S (precompLinear R F t₃ n)) (n : ℕ) :
    IsLocalizedModule S (precompLinear R F t₄ n) := by
  have hprod : ∀ n, IsLocalizedModule S ((precompLinear R F t₂ n).prodMap (precompLinear R F t₃ n)) :=
    fun n => by have := h₂ n; have := h₃ n; infer_instance
  have hprod_apply : ∀ n (p : Ext sq.X₂ F n × Ext sq.X₃ F n),
      (precompLinear R F t₂ n).prodMap (precompLinear R F t₃ n) p =
        Prod.map (precompLinear R F t₂ n) (precompLinear R F t₃ n) p := fun n p => rfl
  cases n with
  | zero =>
    have := h₁ 0
    have := hprod 0
    have : IsLocalizedModule S (0 : PUnit.{1} →ₗ[R] PUnit.{1}) := IsLocalizedModule.of_subsingleton S _
    refine IsLocalizedModule.of_exact_ladder S (0 : PUnit.{1} →ₗ[R] PUnit.{1}) (0 : PUnit.{1} →ₗ[R] Ext sq.X₄ F 0)
      (mvToProd R F sq 0) (mvFromProd R F sq 0)
      (0 : PUnit.{1} →ₗ[R] PUnit.{1}) (0 : PUnit.{1} →ₗ[R] Ext sq'.X₄ F 0) (mvToProd R F sq' 0) (mvFromProd R F sq' 0)
      0 0 (precompLinear R F t₄ 0) ((precompLinear R F t₂ 0).prodMap (precompLinear R F t₃ 0))
      (precompLinear R F t₁ 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x; rfl
    · intro x; simp
    · intro x; rw [hprod_apply, mvToProd_precompLinear R F sq' sq t₂ t₃ t₄ c₂₄ c₃₄]
    · intro x; rw [hprod_apply, mvFromProd_precompLinear R F sq' sq t₁ t₂ t₃ c₁₂ c₁₃]
    · intro y; simp
    · intro y
      simp only [LinearMap.zero_apply, Set.mem_range, exists_const]
      exact ⟨fun hy => (mvToProd_zero_injective R F sq hS (hy.trans (map_zero _).symm)).symm,
        fun hy => by rw [← hy, map_zero]⟩
    · exact mv_exact_toProd_fromProd R F sq hS 0
    · intro y; simp
    · intro y
      simp only [LinearMap.zero_apply, Set.mem_range, exists_const]
      exact ⟨fun hy => (mvToProd_zero_injective R F sq' hS' (hy.trans (map_zero _).symm)).symm,
        fun hy => by rw [← hy, map_zero]⟩
    · exact mv_exact_toProd_fromProd R F sq' hS' 0
  | succ m =>
    have := h₁ m
    have := h₁ (m + 1)
    have := hprod m
    have := hprod (m + 1)
    refine IsLocalizedModule.of_exact_ladder S (mvFromProd R F sq m) (mvDelta R F sq hS m (m + 1) rfl)
      (mvToProd R F sq (m + 1)) (mvFromProd R F sq (m + 1))
      (mvFromProd R F sq' m) (mvDelta R F sq' hS' m (m + 1) rfl) (mvToProd R F sq' (m + 1))
      (mvFromProd R F sq' (m + 1))
      ((precompLinear R F t₂ m).prodMap (precompLinear R F t₃ m)) (precompLinear R F t₁ m)
      (precompLinear R F t₄ (m + 1)) ((precompLinear R F t₂ (m + 1)).prodMap (precompLinear R F t₃ (m + 1)))
      (precompLinear R F t₁ (m + 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro p; rw [hprod_apply, mvFromProd_precompLinear R F sq' sq t₁ t₂ t₃ c₁₂ c₁₃]
    · intro x; rw [mvDelta_precompLinear R F sq' sq t₁ t₂ t₃ t₄ c₁₂ c₁₃ c₂₄ c₃₄ hS' hS]
    · intro x; rw [hprod_apply, mvToProd_precompLinear R F sq' sq t₂ t₃ t₄ c₂₄ c₃₄]
    · intro p; rw [hprod_apply, mvFromProd_precompLinear R F sq' sq t₁ t₂ t₃ c₁₂ c₁₃]
    · exact mv_exact_fromProd_delta R F sq hS m (m + 1) rfl
    · exact mv_exact_delta_toProd R F sq hS m (m + 1) rfl
    · exact mv_exact_toProd_fromProd R F sq hS (m + 1)
    · exact mv_exact_fromProd_delta R F sq' hS' m (m + 1) rfl
    · exact mv_exact_delta_toProd R F sq' hS' m (m + 1) rfl
    · exact mv_exact_toProd_fromProd R F sq' hS' (m + 1)


/-- `isLocalizedModule_precompLinear_of_mv` with the two squares given by their objects and maps
(so that, when applied, all `Ext` groups are stated on the given objects and no projection of a
`Square` structure has to be unfolded by the kernel). -/
theorem isLocalizedModule_precompLinear_of_mv' {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C}
    (f₁₂ : A₁ ⟶ A₂) (f₁₃ : A₁ ⟶ A₃) (f₂₄ : A₂ ⟶ A₄) (f₃₄ : A₃ ⟶ A₄) (fac : f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄)
    (g₁₂ : B₁ ⟶ B₂) (g₁₃ : B₁ ⟶ B₃) (g₂₄ : B₂ ⟶ B₄) (g₃₄ : B₃ ⟶ B₄) (fac' : g₁₂ ≫ g₂₄ = g₁₃ ≫ g₃₄)
    (hS : (Square.mk f₁₂ f₁₃ f₂₄ f₃₄ fac).mvShortComplex.ShortExact)
    (hS' : (Square.mk g₁₂ g₁₃ g₂₄ g₃₄ fac').mvShortComplex.ShortExact)
    (t₁ : B₁ ⟶ A₁) (t₂ : B₂ ⟶ A₂) (t₃ : B₃ ⟶ A₃) (t₄ : B₄ ⟶ A₄)
    (c₁₂ : g₁₂ ≫ t₂ = t₁ ≫ f₁₂) (c₁₃ : g₁₃ ≫ t₃ = t₁ ≫ f₁₃)
    (c₂₄ : g₂₄ ≫ t₄ = t₂ ≫ f₂₄) (c₃₄ : g₃₄ ≫ t₄ = t₃ ≫ f₃₄)
    (h₁ : ∀ n, IsLocalizedModule S (precompLinear R F t₁ n))
    (h₂ : ∀ n, IsLocalizedModule S (precompLinear R F t₂ n))
    (h₃ : ∀ n, IsLocalizedModule S (precompLinear R F t₃ n)) (n : ℕ) :
    IsLocalizedModule S (precompLinear R F t₄ n) :=
  isLocalizedModule_precompLinear_of_mv R F S (Square.mk g₁₂ g₁₃ g₂₄ g₃₄ fac')
    (Square.mk f₁₂ f₁₃ f₂₄ f₃₄ fac) hS' hS t₁ t₂ t₃ t₄ c₁₂ c₁₃ c₂₄ c₃₄ h₁ h₂ h₃ n

end Induction

end CategoryTheory.Abelian.Ext

end
