import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_WhiskerAdd
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc

/-! # The truncated jet algebra

The truncated jet algebra `⊕_{q=0}^{κ} L^{-q}`, with products of weight greater than `κ` set to zero, is a
quasi-coherent `O`-algebra on `C̃` (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The `q`-th piece `M^{⊗q}` (`M = L^{-1} := (L.zpow (-1)).toModules`; tensor powers are defined recursively with the
monoidal structure of `X.Modules`, the `0`-th power being `𝟙_ = O`). -/

noncomputable def truncatedJetAlgebra.piece {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) : ℕ → Ct.toScheme.Modules
  | 0 => 𝟙_ Ct.toScheme.Modules
  | q + 1 => truncatedJetAlgebra.piece L q ⊗ (L.zpow (-1)).toModules

/-- The canonical multiplication `M^{⊗a} ⊗ M^{⊗b} ⟶ M^{⊗(a+b)}`: recursion on `b`, using the right unitor for `b = 0`
and the associator for `b + 1`. -/

noncomputable def truncatedJetAlgebra.pieceMul {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (a : ℕ) :
    ∀ b : ℕ, truncatedJetAlgebra.piece L a ⊗ truncatedJetAlgebra.piece L b ⟶
      truncatedJetAlgebra.piece L (a + b)
  | 0 => (ρ_ (truncatedJetAlgebra.piece L a)).hom
  | b + 1 => (α_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b)
        (L.zpow (-1)).toModules).inv ≫
      (truncatedJetAlgebra.pieceMul L a b ▷ (L.zpow (-1)).toModules)

/-- The underlying sheaf of modules `⊕_{q ≤ κ} M^{⊗q}`. -/

noncomputable abbrev truncatedJetAlgebra.obj {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) : Ct.toScheme.Modules :=
  CategoryTheory.Limits.biproduct (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)

/-- The multiplication `Σ_{a+b ≤ κ} (π_a ⊗ π_b) ≫ m_{a,b} ≫ ι_{a+b}` (products of weight greater than `κ` are zero). -/

noncomputable def truncatedJetAlgebra.mulHom {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    truncatedJetAlgebra.obj L κ ⊗ truncatedJetAlgebra.obj L κ ⟶ truncatedJetAlgebra.obj L κ :=
  ∑ a : Fin (κ + 1), ∑ b : Fin (κ + 1),
    if h : a.val + b.val ≤ κ then
      CategoryTheory.MonoidalCategory.tensorHom
          (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) a)
          (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) b) ≫
        truncatedJetAlgebra.pieceMul L a b ≫
        CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨a.val + b.val, Nat.lt_succ_of_le h⟩
    else 0

/-- The unit `ι_0`. -/

noncomputable def truncatedJetAlgebra.oneHom {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) : 𝟙_ Ct.toScheme.Modules ⟶ truncatedJetAlgebra.obj L κ :=
  CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
    ⟨0, Nat.succ_pos κ⟩

/- The four algebra axioms of `truncatedJetAlgebra` are stated as separate named theorems so that they can be
   referenced individually downstream. -/

/-- Every piece `M^{⊗q}` is a line bundle (induction on `q`: `O` is a line bundle, and a tensor product of line
bundles is a line bundle). -/
instance truncatedJetAlgebra.piece_isLineBundle {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) : ∀ q : ℕ, (truncatedJetAlgebra.piece L q).IsLineBundle
  | 0 => AlgebraicGeometry.Scheme.Modules.IsLineBundle.unit Ct.toScheme
  | q + 1 =>
    have := truncatedJetAlgebra.piece_isLineBundle L q
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (truncatedJetAlgebra.piece L q)
        (L.zpow (-1)).toModules)

/-- Finite biproducts preserve quasi-coherence (the finite special case of Stacks 01ID). Reduces to
`isQuasicoherent_biproduct_of_fintype` (`⨁ M ≅ colimit (Discrete.functor (M ∘ ULift.down))`, then
`isQuasicoherent_colimit`); `Finite J` becomes `Fintype J` through `Fintype.ofFinite` (`HasBiproduct` is a `Prop`,
so the instance path does not affect the statement). -/
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type} [Finite J] (M : J → X.Modules) (hM : ∀ j, (M j).IsQuasicoherent) :
    (CategoryTheory.Limits.biproduct M).IsQuasicoherent := by
  have := Fintype.ofFinite J
  exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct_of_fintype M hM

/-- Every piece is quasi-coherent: `piece_isLineBundle` ⇒ locally free (`IsLineBundle.isLocallyFree`) ⇒
quasi-coherent (the general form, locally free ⇒ quasi-coherent, is `isQuasicoherent_of_isLocallyFree`). -/
theorem truncatedJetAlgebra.piece_isQuasicoherent {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (q : ℕ) : (truncatedJetAlgebra.piece L q).IsQuasicoherent :=
  -- locally free ⇒ quasi-coherent
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _

/-- Quasi-coherence: every piece is quasi-coherent, then apply `isQuasicoherent_biproduct`. -/
theorem truncatedJetAlgebra.obj_isQuasicoherent {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) : (truncatedJetAlgebra.obj L κ).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct _ fun q =>
    truncatedJetAlgebra.piece_isQuasicoherent L q

/-! ## Componentwise tools

The three algebra laws are all proved piece by piece, using "a morphism out of `(⨁ P) ⊗ (⨁ P)` is determined by the
components `ι_a ⊗ₘ ι_b`": `𝟙 (⨁ P) = ∑ π_j ≫ ι_j` (`biproduct.total`), and `⊗` is bilinear for the preadditive
structure (`monoidalPreadditive`, used through a local `letI`, not registered as a global instance).
The single-whisker versions `biproduct_whiskerRight_hom_ext` / `biproduct_whiskerLeft_hom_ext` are in
`DeformedJetAlgebra_WhiskerAdd.lean`. All names live in the `truncatedJetAlgebra` namespace to avoid clashing with
`AlgebraicGeometry.Scheme.Modules.biproduct_tensor_biproduct_hom_ext` of `DeformedJetAlgebra.lean`. -/

namespace truncatedJetAlgebra

/-- A morphism out of `(⨁ F) ⊗ (⨁ G)` is determined by the `ι_j ⊗ₘ ι_k` (`tensorHom_def'` splits it into two whiskers,
each handled by a single-whisker extensionality lemma). -/
theorem biproduct_tensor_hom_ext {X : AlgebraicGeometry.Scheme.{u}}
    {J K : Type} [Fintype J] [Fintype K] (F : J → X.Modules) (G : K → X.Modules) {Z : X.Modules}
    {g h : CategoryTheory.Limits.biproduct F ⊗ CategoryTheory.Limits.biproduct G ⟶ Z}
    (w : ∀ j k, (CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ≫ g =
      (CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ≫ h) : g = h := by
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerRight_hom_ext F (CategoryTheory.Limits.biproduct G)
  intro j
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerLeft_hom_ext (F j) G
  intro k
  rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.MonoidalCategory.tensorHom_def', w j k]

/-- A morphism out of `((⨁ F) ⊗ (⨁ G)) ⊗ N` is determined by the `(ι_j ⊗ₘ ι_k) ▷ N`:
`𝟙 ((⨁F) ⊗ (⨁G)) = ∑_{j,k} (π_j ⊗ₘ π_k) ≫ (ι_j ⊗ₘ ι_k)` (bilinearity + `biproduct.total`), then whisker on the right. -/
theorem biproduct_tensor_whiskerRight_hom_ext {X : AlgebraicGeometry.Scheme.{u}}
    {J K : Type} [Fintype J] [Fintype K] (F : J → X.Modules) (G : K → X.Modules) (N : X.Modules) {Z : X.Modules}
    {g h : (CategoryTheory.Limits.biproduct F ⊗ CategoryTheory.Limits.biproduct G) ⊗ N ⟶ Z}
    (w : ∀ j k, ((CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ▷ N) ≫ g =
      ((CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ▷ N) ≫ h) : g = h := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  have htot : CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.biproduct F ⊗ CategoryTheory.Limits.biproduct G) =
      ∑ j : J, ∑ k : K,
        (CategoryTheory.Limits.biproduct.π F j ⊗ₘ CategoryTheory.Limits.biproduct.π G k) ≫
          (CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) := by
    rw [← CategoryTheory.MonoidalCategory.id_tensorHom_id, ← CategoryTheory.Limits.biproduct.total,
      ← CategoryTheory.Limits.biproduct.total, CategoryTheory.sum_tensor]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CategoryTheory.tensor_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
  have htot' : CategoryTheory.CategoryStruct.id ((CategoryTheory.Limits.biproduct F ⊗ CategoryTheory.Limits.biproduct G) ⊗ N) =
      ∑ j : J, ∑ k : K,
        ((CategoryTheory.Limits.biproduct.π F j ⊗ₘ CategoryTheory.Limits.biproduct.π G k) ▷ N) ≫
          ((CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ▷ N) := by
    rw [← CategoryTheory.MonoidalCategory.id_whiskerRight, htot, CategoryTheory.sum_whiskerRight]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CategoryTheory.sum_whiskerRight]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [CategoryTheory.MonoidalCategory.comp_whiskerRight]
  calc g = CategoryTheory.CategoryStruct.id _ ≫ g := (Category.id_comp g).symm
    _ = ∑ j : J, ∑ k : K, ((CategoryTheory.Limits.biproduct.π F j ⊗ₘ CategoryTheory.Limits.biproduct.π G k) ▷ N) ≫
          (((CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ▷ N) ≫ g) := by
      rw [htot', Preadditive.sum_comp]
      simp only [Preadditive.sum_comp, Category.assoc]
    _ = ∑ j : J, ∑ k : K, ((CategoryTheory.Limits.biproduct.π F j ⊗ₘ CategoryTheory.Limits.biproduct.π G k) ▷ N) ≫
          (((CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ▷ N) ≫ h) := by
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [w j k]
    _ = CategoryTheory.CategoryStruct.id _ ≫ h := by
      rw [htot', Preadditive.sum_comp]
      simp only [Preadditive.sum_comp, Category.assoc]
    _ = h := Category.id_comp h

/-- A morphism out of `((⨁ F) ⊗ (⨁ G)) ⊗ (⨁ H)` is determined by the `(ι_j ⊗ₘ ι_k) ⊗ₘ ι_l`. -/
theorem biproduct_tensor_tensor_hom_ext {X : AlgebraicGeometry.Scheme.{u}}
    {J K L : Type} [Fintype J] [Fintype K] [Fintype L] (F : J → X.Modules) (G : K → X.Modules) (H : L → X.Modules)
    {Z : X.Modules}
    {g h : (CategoryTheory.Limits.biproduct F ⊗ CategoryTheory.Limits.biproduct G) ⊗ CategoryTheory.Limits.biproduct H ⟶ Z}
    (w : ∀ j k l, ((CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ⊗ₘ
        CategoryTheory.Limits.biproduct.ι H l) ≫ g =
      ((CategoryTheory.Limits.biproduct.ι F j ⊗ₘ CategoryTheory.Limits.biproduct.ι G k) ⊗ₘ
        CategoryTheory.Limits.biproduct.ι H l) ≫ h) : g = h := by
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerLeft_hom_ext _ H
  intro l
  apply biproduct_tensor_whiskerRight_hom_ext F G (H l)
  intro j k
  rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.MonoidalCategory.tensorHom_def, w j k l]

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety)

/-- The component formula for `mulHom`: `(ι_a ⊗ₘ ι_b) ≫ mulHom = [a + b ≤ κ] m_{a,b} ≫ ι_{a+b}` (indices written as
naturals with bounds, convenient for nested use). Proof: expand the double sum; `ι_a ≫ π_{a'}` survives only for
`a' = a` (`biproduct.ι_π_self` / `ι_π_ne`, `tensor_zero`), then `Finset.sum_eq_single` twice. -/
theorem ι_tensor_ι_comp_mulHom (κ : ℕ) (a b : ℕ) (ha : a < κ + 1) (hb : b < κ + 1) :
    (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨a, ha⟩ ⊗ₘ
        CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨b, hb⟩) ≫
      truncatedJetAlgebra.mulHom L κ =
    if h : a + b ≤ κ then
      truncatedJetAlgebra.pieceMul L a b ≫
        CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨a + b, Nat.lt_succ_of_le h⟩
    else 0 := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive Ct.toScheme
  unfold truncatedJetAlgebra.mulHom
  rw [Preadditive.comp_sum, Finset.sum_eq_single (⟨a, ha⟩ : Fin (κ + 1))]
  · rw [Preadditive.comp_sum, Finset.sum_eq_single (⟨b, hb⟩ : Fin (κ + 1))]
    · split_ifs with h
      · rw [← Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
          CategoryTheory.Limits.biproduct.ι_π_self, CategoryTheory.Limits.biproduct.ι_π_self,
          CategoryTheory.MonoidalCategory.tensorHom_id, CategoryTheory.MonoidalCategory.id_whiskerRight,
          Category.id_comp]
      · rw [comp_zero]
    · intro b' _ hb'
      split_ifs
      · rw [← Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
          CategoryTheory.Limits.biproduct.ι_π_ne _ (Ne.symm hb'), CategoryTheory.MonoidalPreadditive.tensor_zero, zero_comp]
      · rw [comp_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ ha'
    rw [Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun b' _ => ?_
    split_ifs
    · rw [← Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
        CategoryTheory.Limits.biproduct.ι_π_ne _ (Ne.symm ha'), CategoryTheory.MonoidalPreadditive.zero_tensor, zero_comp]
    · rw [comp_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `eqToHom` is absorbed by the `ι` of a biproduct: `eqToHom h ≫ ι_j = ι_i` (`i = j`; `h` arbitrary, for `rw`
matching). -/
theorem eqToHom_comp_ι (κ : ℕ) {i j : ℕ} (hij : i = j) (hj : j < κ + 1)
    (h : truncatedJetAlgebra.piece L i = truncatedJetAlgebra.piece L j) :
    CategoryTheory.eqToHom h ≫
        CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨j, hj⟩ =
      CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨i, hij ▸ hj⟩ := by
  subst hij
  simp

end truncatedJetAlgebra

/-! ## Pure coherence lemmas (in an arbitrary (symmetric) monoidal category)

After the piecewise reduction the three laws only involve monoidal coherence; the lemmas are stated in a general
category to avoid `simp` on the heavy instances of `X.Modules`. -/

section Coherence

open CategoryTheory.MonoidalCategory

namespace truncatedJetAlgebra.Coh

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]

/-- Induction step for the left unitor: `α⁻¹ ≫ ((λ_ B).hom ≫ e) ▷ V = (λ_ (B ⊗ V)).hom ≫ (e ▷ V)`. -/
theorem zero_left_step {B B' V : C} (e : B ⟶ B') :
    (α_ (𝟙_ C) B V).inv ≫ (((λ_ B).hom ≫ e) ▷ V) = (λ_ (B ⊗ V)).hom ≫ (e ▷ V) := by
  rw [comp_whiskerRight, leftUnitor_tensor_hom, Category.assoc]

/-- Base case `c = 0` of associativity: `(m ▷ 𝟙_) ≫ ρ_ = α ≫ (A ◁ ρ_) ≫ m`. -/
theorem assoc_zero {A B W : C} (m : A ⊗ B ⟶ W) :
    (m ▷ 𝟙_ C) ≫ (ρ_ W).hom = (α_ A B (𝟙_ C)).hom ≫ (A ◁ (ρ_ B).hom) ≫ m := by
  rw [rightUnitor_naturality, rightUnitor_tensor_hom, Category.assoc]

/-- Induction step of associativity (the pentagon axiom). -/
theorem assoc_step {A B P V W W' U U' : C} (mab : A ⊗ B ⟶ W) (mbc : B ⊗ P ⟶ W')
    (mabc : W ⊗ P ⟶ U) (mabc' : A ⊗ W' ⟶ U') (e : U' ⟶ U)
    (IH : (mab ▷ P) ≫ mabc = (α_ A B P).hom ≫ (A ◁ mbc) ≫ mabc' ≫ e) :
    (mab ▷ (P ⊗ V)) ≫ (α_ W P V).inv ≫ (mabc ▷ V) =
      (α_ A B (P ⊗ V)).hom ≫ (A ◁ ((α_ B P V).inv ≫ (mbc ▷ V))) ≫ (α_ A W' V).inv ≫
        (mabc' ▷ V) ≫ (e ▷ V) := by
  rw [whiskerRight_tensor, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight, IH, comp_whiskerRight, comp_whiskerRight, comp_whiskerRight, whisker_assoc,
    whiskerLeft_comp]
  simp only [Category.assoc, pentagon_inv_hom_hom_hom_inv_assoc]

variable [BraidedCategory C]

/-- Formula for multiplying by one `M` on the left, base case `a = 0`. -/
theorem succ_left_zero (B V : C) :
    (ρ_ (B ⊗ V)).hom =
      (α_ B V (𝟙_ C)).hom ≫ (B ◁ (β_ V (𝟙_ C)).hom) ≫ (α_ B (𝟙_ C) V).inv ≫ ((ρ_ B).hom ▷ V) := by
  rw [braiding_tensorUnit_right, whiskerLeft_comp, Category.assoc, triangle_assoc_comp_left_inv_assoc,
    ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id, rightUnitor_tensor_hom]

/-- Formula for multiplying by one `M` on the left, induction step (needs `β_{V,V} = 𝟙`). -/
theorem succ_left_step {B V A W : C} (hβ : (β_ V V).hom = 𝟙 _) (n : (B ⊗ A) ⊗ V ⟶ W) :
    (α_ (B ⊗ V) A V).inv ≫ (((α_ B V A).hom ≫ (B ◁ (β_ V A).hom) ≫ (α_ B A V).inv ≫ n) ▷ V) =
      (α_ B V (A ⊗ V)).hom ≫ (B ◁ (β_ V (A ⊗ V)).hom) ≫ (α_ B (A ⊗ V) V).inv ≫
        (((α_ B A V).inv ≫ n) ▷ V) := by
  rw [BraidedCategory.braiding_tensor_right_hom, hβ, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id, Category.comp_id]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc, whisker_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc]

end truncatedJetAlgebra.Coh

namespace truncatedJetAlgebra.Coh

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Induction step of commutativity (symmetry `β ≫ β = 𝟙`). -/
theorem comm_step {A B V W W' : C} (m : A ⊗ B ⟶ W) (n : B ⊗ A ⟶ W') (e : W ⟶ W')
    (IH : (β_ A B).hom ≫ n = m ≫ e) :
    (β_ A (B ⊗ V)).hom ≫ (α_ B V A).hom ≫ (B ◁ (β_ V A).hom) ≫ (α_ B A V).inv ≫ (n ▷ V) =
      (α_ A B V).inv ≫ (m ▷ V) ≫ (e ▷ V) := by
  rw [BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id_assoc, ← comp_whiskerRight, IH, comp_whiskerRight]

/-- Right-associated form of `comm_step` (followed by an arbitrary `h`; `reassoc_of%` gets stuck on the heavy
instances of `X.Modules`, so this is done in a general category). -/
theorem comm_step_assoc {A B V W W' Z : C} (m : A ⊗ B ⟶ W) (n : B ⊗ A ⟶ W') (e : W ⟶ W') (h : W' ⊗ V ⟶ Z)
    (IH : (β_ A B).hom ≫ n = m ≫ e) :
    (β_ A (B ⊗ V)).hom ≫ (α_ B V A).hom ≫ (B ◁ (β_ V A).hom) ≫ (α_ B A V).inv ≫ (n ▷ V) ≫ h =
      (α_ A B V).inv ≫ (m ▷ V) ≫ (e ▷ V) ≫ h := by
  simpa only [Category.assoc] using congrArg (· ≫ h) (comm_step (V := V) m n e IH)

end truncatedJetAlgebra.Coh


end Coherence

namespace truncatedJetAlgebra

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety)

/-- `m_{0,b} = λ_ ≫ eqToHom`: induction on `b`; `b = 0` is `unitors_equal`, `b + 1` uses `leftUnitor_tensor_hom`
(`Coh.zero_left_step`). -/
theorem pieceMul_zero_left (b : ℕ) :
    truncatedJetAlgebra.pieceMul L 0 b =
      (λ_ (truncatedJetAlgebra.piece L b)).hom ≫
        CategoryTheory.eqToHom (congrArg (truncatedJetAlgebra.piece L) (Nat.zero_add b).symm) := by
  induction b with
  | zero =>
    show (ρ_ (𝟙_ Ct.toScheme.Modules)).hom = (λ_ (𝟙_ Ct.toScheme.Modules)).hom ≫ CategoryTheory.eqToHom rfl
    rw [CategoryTheory.eqToHom_refl, Category.comp_id, CategoryTheory.MonoidalCategory.unitors_equal]
  | succ b ih =>
    rw [truncatedJetAlgebra.pieceMul, ih]
    dsimp only [truncatedJetAlgebra.piece]
    rw [truncatedJetAlgebra.Coh.zero_left_step, CategoryTheory.MonoidalCategory.eqToHom_whiskerRight]

/-- Associativity of `pieceMul` (up to an `eqToHom` re-indexing `a + b + c`): induction on `c`; `c = 0` is the
naturality of the right unitor + `rightUnitor_tensor_hom`, the induction step is the pentagon axiom
(`Coh.assoc_zero` / `Coh.assoc_step`). -/
theorem pieceMul_assoc (a b c : ℕ) :
    (truncatedJetAlgebra.pieceMul L a b ▷ truncatedJetAlgebra.piece L c) ≫
        truncatedJetAlgebra.pieceMul L (a + b) c =
      (α_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b) (truncatedJetAlgebra.piece L c)).hom ≫
        (truncatedJetAlgebra.piece L a ◁ truncatedJetAlgebra.pieceMul L b c) ≫
        truncatedJetAlgebra.pieceMul L a (b + c) ≫
        CategoryTheory.eqToHom (congrArg (truncatedJetAlgebra.piece L) (Nat.add_assoc a b c).symm) := by
  induction c with
  | zero =>
    show (truncatedJetAlgebra.pieceMul L a b ▷ 𝟙_ Ct.toScheme.Modules) ≫
        (ρ_ (truncatedJetAlgebra.piece L (a + b))).hom =
      (α_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b) (𝟙_ Ct.toScheme.Modules)).hom ≫
        (truncatedJetAlgebra.piece L a ◁ (ρ_ (truncatedJetAlgebra.piece L b)).hom) ≫
        truncatedJetAlgebra.pieceMul L a b ≫ CategoryTheory.eqToHom rfl
    rw [CategoryTheory.eqToHom_refl, Category.comp_id, truncatedJetAlgebra.Coh.assoc_zero]
  | succ c ih =>
    show (truncatedJetAlgebra.pieceMul L a b ▷ (truncatedJetAlgebra.piece L c ⊗ (L.zpow (-1)).toModules)) ≫
        (α_ (truncatedJetAlgebra.piece L (a + b)) (truncatedJetAlgebra.piece L c) (L.zpow (-1)).toModules).inv ≫
        (truncatedJetAlgebra.pieceMul L (a + b) c ▷ (L.zpow (-1)).toModules) =
      (α_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b)
          (truncatedJetAlgebra.piece L c ⊗ (L.zpow (-1)).toModules)).hom ≫
        (truncatedJetAlgebra.piece L a ◁
          ((α_ (truncatedJetAlgebra.piece L b) (truncatedJetAlgebra.piece L c) (L.zpow (-1)).toModules).inv ≫
            (truncatedJetAlgebra.pieceMul L b c ▷ (L.zpow (-1)).toModules))) ≫
        ((α_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L (b + c)) (L.zpow (-1)).toModules).inv ≫
          (truncatedJetAlgebra.pieceMul L a (b + c) ▷ (L.zpow (-1)).toModules)) ≫
        CategoryTheory.eqToHom (congrArg (truncatedJetAlgebra.piece L) (Nat.add_assoc a b (c + 1)).symm)
    rw [truncatedJetAlgebra.Coh.assoc_step _ _ _ _ _ ih, CategoryTheory.MonoidalCategory.eqToHom_whiskerRight]
    simp only [Category.assoc]
    rfl

/-- The braiding on the line bundle `M = L^{-1}` is the identity (`braiding_hom_eq_id_of_isLineBundle`, Stacks 01CR). -/
theorem braiding_gen_eq_id :
    (β_ (L.zpow (-1)).toModules (L.zpow (-1)).toModules).hom = 𝟙 _ :=
  AlgebraicGeometry.Scheme.Modules.braiding_hom_eq_id_of_isLineBundle (L.zpow (-1)).toModules

/-- Move one `M` from the left to the right:
`m_{b+1,a} = α ≫ (M^{⊗b} ◁ β_{M,M^{⊗a}}) ≫ α⁻¹ ≫ (m_{b,a} ▷ M) ≫ eqToHom`. Induction on `a`: `a = 0` is
`Coh.succ_left_zero` (the triangle axiom), the induction step `Coh.succ_left_step` uses `β_{M,M} = 𝟙`
(**this step uses that `M` is a line bundle**) and the pentagon axiom. -/
theorem pieceMul_succ_left (b a : ℕ) :
    truncatedJetAlgebra.pieceMul L (b + 1) a =
      (α_ (truncatedJetAlgebra.piece L b) (L.zpow (-1)).toModules (truncatedJetAlgebra.piece L a)).hom ≫
        (truncatedJetAlgebra.piece L b ◁ (β_ (L.zpow (-1)).toModules (truncatedJetAlgebra.piece L a)).hom) ≫
        (α_ (truncatedJetAlgebra.piece L b) (truncatedJetAlgebra.piece L a) (L.zpow (-1)).toModules).inv ≫
        (truncatedJetAlgebra.pieceMul L b a ▷ (L.zpow (-1)).toModules) ≫
        CategoryTheory.eqToHom (congrArg (truncatedJetAlgebra.piece L) (Nat.add_right_comm b a 1)) := by
  induction a with
  | zero =>
    show (ρ_ (truncatedJetAlgebra.piece L b ⊗ (L.zpow (-1)).toModules)).hom =
      (α_ (truncatedJetAlgebra.piece L b) (L.zpow (-1)).toModules (𝟙_ Ct.toScheme.Modules)).hom ≫
        (truncatedJetAlgebra.piece L b ◁ (β_ (L.zpow (-1)).toModules (𝟙_ Ct.toScheme.Modules)).hom) ≫
        (α_ (truncatedJetAlgebra.piece L b) (𝟙_ Ct.toScheme.Modules) (L.zpow (-1)).toModules).inv ≫
        ((ρ_ (truncatedJetAlgebra.piece L b)).hom ▷ (L.zpow (-1)).toModules) ≫ CategoryTheory.eqToHom rfl
    rw [CategoryTheory.eqToHom_refl, Category.comp_id]
    exact truncatedJetAlgebra.Coh.succ_left_zero _ _
  | succ a ih =>
    simp only [truncatedJetAlgebra.pieceMul]
    rw [ih]
    dsimp only [truncatedJetAlgebra.piece]
    rw [truncatedJetAlgebra.Coh.succ_left_step (truncatedJetAlgebra.braiding_gen_eq_id L)]
    simp only [CategoryTheory.MonoidalCategory.comp_whiskerRight, Category.assoc]
    erw [CategoryTheory.MonoidalCategory.eqToHom_whiskerRight]

/-- Commutativity of `pieceMul` (up to the `eqToHom` of `a + b = b + a`): induction on `b`; `b = 0` is
`braiding_leftUnitor` + `pieceMul_zero_left`; the induction step expands `m_{b+1,a}` with `pieceMul_succ_left` and
reduces to the induction hypothesis by `Coh.comm_step` (`braiding_tensor_right_hom` + symmetry `β ≫ β = 𝟙`).
**`M` being a line bundle** is used only in `pieceMul_succ_left`. -/
theorem pieceMul_comm (a b : ℕ) :
    (β_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b)).hom ≫
        truncatedJetAlgebra.pieceMul L b a =
      truncatedJetAlgebra.pieceMul L a b ≫
        CategoryTheory.eqToHom (congrArg (truncatedJetAlgebra.piece L) (Nat.add_comm a b)) := by
  induction b with
  | zero =>
    show (β_ (truncatedJetAlgebra.piece L a) (𝟙_ Ct.toScheme.Modules)).hom ≫ truncatedJetAlgebra.pieceMul L 0 a =
      (ρ_ (truncatedJetAlgebra.piece L a)).hom ≫ CategoryTheory.eqToHom _
    rw [truncatedJetAlgebra.pieceMul_zero_left, ← Category.assoc, CategoryTheory.braiding_leftUnitor]
  | succ b ih =>
    show (β_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b ⊗ (L.zpow (-1)).toModules)).hom ≫
        truncatedJetAlgebra.pieceMul L (b + 1) a =
      ((α_ (truncatedJetAlgebra.piece L a) (truncatedJetAlgebra.piece L b) (L.zpow (-1)).toModules).inv ≫
        (truncatedJetAlgebra.pieceMul L a b ▷ (L.zpow (-1)).toModules)) ≫
        CategoryTheory.eqToHom (congrArg (truncatedJetAlgebra.piece L) (Nat.add_comm a (b + 1)))
    rw [truncatedJetAlgebra.pieceMul_succ_left,
      truncatedJetAlgebra.Coh.comm_step_assoc (truncatedJetAlgebra.pieceMul L a b)
        (truncatedJetAlgebra.pieceMul L b a)
        (CategoryTheory.eqToHom (congrArg (truncatedJetAlgebra.piece L) (Nat.add_comm a b))) _ ih,
      CategoryTheory.MonoidalCategory.eqToHom_whiskerRight, Category.assoc]
    erw [CategoryTheory.eqToHom_trans]

end truncatedJetAlgebra

/-- Left unit law. Both sides are morphisms out of `𝟙 ⊗ (⊕ M^{⊗q})`; compare them piecewise with
`biproduct_whiskerLeft_hom_ext`. The left side becomes `λ_ ≫ ι_b` by naturality of the left unitor, the right side
becomes `m_{0,b} ≫ ι_{0+b}` by the component formula `ι_tensor_ι_comp_mulHom` (`a = 0`); then `pieceMul_zero_left`
(`m_{0,b} = λ_ ≫ eqToHom`), and `eqToHom` is absorbed by `eqToHom_comp_ι`. -/
theorem truncatedJetAlgebra.one_mul {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (λ_ (truncatedJetAlgebra.obj L κ)).hom =
      (truncatedJetAlgebra.oneHom L κ ▷ truncatedJetAlgebra.obj L κ) ≫ truncatedJetAlgebra.mulHom L κ := by
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerLeft_hom_ext
  rintro ⟨b, hb⟩
  rw [CategoryTheory.MonoidalCategory.leftUnitor_naturality, ← Category.assoc,
    ← CategoryTheory.MonoidalCategory.tensorHom_def']
  unfold truncatedJetAlgebra.oneHom
  erw [truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ 0 b (Nat.succ_pos κ) hb]
  rw [dif_pos (by omega)]
  dsimp only [truncatedJetAlgebra.piece]
  rw [truncatedJetAlgebra.pieceMul_zero_left, Category.assoc,
    truncatedJetAlgebra.eqToHom_comp_ι L κ (Nat.zero_add b).symm]

/-- Associativity. Compare piecewise in `(a, b, c)` with `biproduct_tensor_tensor_hom_ext`; naturality of the
associator, `tensorHom_comp_whiskerLeft` / `tensorHom_comp_whiskerRight` and the component formula (twice) reduce
the two sides to `α ≫ (M^{⊗a} ◁ m_{b,c}) ≫ m_{a,b+c} ≫ ι` and `(m_{a,b} ▷ M^{⊗c}) ≫ m_{a+b,c} ≫ ι`; then
`pieceMul_assoc` (induction on `c`, the induction step being the pentagon axiom), and `eqToHom` is absorbed by
`eqToHom_comp_ι`. Truncation: for `a+b+c > κ` both sides are `0` (directly if `a+b > κ` or `b+c > κ`, otherwise
the outermost `if` is `0`). -/
theorem truncatedJetAlgebra.mul_assoc {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (α_ (truncatedJetAlgebra.obj L κ) (truncatedJetAlgebra.obj L κ) (truncatedJetAlgebra.obj L κ)).hom ≫
        (truncatedJetAlgebra.obj L κ ◁ truncatedJetAlgebra.mulHom L κ) ≫ truncatedJetAlgebra.mulHom L κ =
      (truncatedJetAlgebra.mulHom L κ ▷ truncatedJetAlgebra.obj L κ) ≫ truncatedJetAlgebra.mulHom L κ := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive Ct.toScheme
  apply truncatedJetAlgebra.biproduct_tensor_tensor_hom_ext
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  rw [CategoryTheory.MonoidalCategory.associator_naturality_assoc, ← Category.assoc (_ ⊗ₘ _),
    CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerLeft,
    truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ b c hb hc, ← Category.assoc ((_ ⊗ₘ _) ⊗ₘ _),
    CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerRight,
    truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ a b ha hb]
  by_cases habc : a + b + c ≤ κ
  · have hab : a + b ≤ κ := by omega
    have hbc : b + c ≤ κ := by omega
    rw [dif_pos hab, dif_pos hbc, ← CategoryTheory.MonoidalCategory.whiskerLeft_comp_tensorHom,
      ← CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom, Category.assoc, Category.assoc,
      truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ a (b + c) ha (Nat.lt_succ_of_le hbc),
      truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ (a + b) c (Nat.lt_succ_of_le hab) hc,
      dif_pos (show a + (b + c) ≤ κ by omega), dif_pos habc,
      reassoc_of% (truncatedJetAlgebra.pieceMul_assoc L a b c),
      truncatedJetAlgebra.eqToHom_comp_ι L κ (Nat.add_assoc a b c).symm]
  · -- truncation: for a + b + c > κ both sides are 0
    refine Eq.trans (b := 0) ?_ (Eq.symm ?_)
    · by_cases hbc : b + c ≤ κ
      · rw [dif_pos hbc, ← CategoryTheory.MonoidalCategory.whiskerLeft_comp_tensorHom, Category.assoc,
          truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ a (b + c) ha (Nat.lt_succ_of_le hbc),
          dif_neg (show ¬ a + (b + c) ≤ κ by omega), comp_zero, comp_zero]
      · rw [dif_neg hbc, CategoryTheory.MonoidalPreadditive.tensor_zero, zero_comp, comp_zero]
    · by_cases hab : a + b ≤ κ
      · rw [dif_pos hab, ← CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom, Category.assoc,
          truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ (a + b) c (Nat.lt_succ_of_le hab) hc, dif_neg habc,
          comp_zero]
      · rw [dif_neg hab, CategoryTheory.MonoidalPreadditive.zero_tensor, zero_comp]

/-- Commutativity. Compare piecewise in `(a, b)` with `biproduct_tensor_hom_ext`; naturality of the braiding + the
component formula reduce to `β_{M^{⊗a},M^{⊗b}} ≫ m_{b,a} ≫ ι_{b+a} = m_{a,b} ≫ ι_{a+b}`, then `pieceMul_comm`.
**This law does not hold for tensor powers of an arbitrary object**: it uses that `M` is a line bundle, on which the
braiding is `β_{M,M} = 𝟙` (`braiding_hom_eq_id_of_isLineBundle`, Stacks 01CR), in the induction step of
`pieceMul_succ_left`. The truncation condition is `a+b ≤ κ ↔ b+a ≤ κ`; otherwise both sides are `0`. -/
theorem truncatedJetAlgebra.mul_comm {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (β_ (truncatedJetAlgebra.obj L κ) (truncatedJetAlgebra.obj L κ)).hom ≫ truncatedJetAlgebra.mulHom L κ =
      truncatedJetAlgebra.mulHom L κ := by
  apply truncatedJetAlgebra.biproduct_tensor_hom_ext
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  rw [← Category.assoc, CategoryTheory.BraidedCategory.braiding_naturality, Category.assoc,
    truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ b a hb ha,
    truncatedJetAlgebra.ι_tensor_ι_comp_mulHom L κ a b ha hb]
  by_cases hab : a + b ≤ κ
  · rw [dif_pos hab, dif_pos (show b + a ≤ κ by omega), reassoc_of% (truncatedJetAlgebra.pieceMul_comm L a b),
      truncatedJetAlgebra.eqToHom_comp_ι L κ (Nat.add_comm a b)]
  · rw [dif_neg hab, dif_neg (show ¬ b + a ≤ κ by omega), comp_zero]

/-- The truncated jet algebra `⊕_{q ≤ κ} M^{⊗q}`, with multiplication `Σ_{a+b ≤ κ} (π_a ⊗ π_b) ≫ m_{a,b} ≫ ι_{a+b}`
(products of weight greater than `κ` are zero) and unit `ι_0`. -/

noncomputable def truncatedJetAlgebra {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    AlgebraicGeometry.Scheme.QCAlgebra Ct.toScheme where
  carrier := truncatedJetAlgebra.obj L κ
  quasicoherent := truncatedJetAlgebra.obj_isQuasicoherent L κ
  mul := truncatedJetAlgebra.mulHom L κ
  one := truncatedJetAlgebra.oneHom L κ
  one_mul := truncatedJetAlgebra.one_mul L κ
  mul_assoc := truncatedJetAlgebra.mul_assoc L κ
  mul_comm := truncatedJetAlgebra.mul_comm L κ

/- The underlying sheaf of modules is `⊕_{q ≤ κ} L^{-q}` (products of weight greater than `κ` are zero):
   `M^{⊗q} ≅ L^{-q}` is given step by step by `zpow_add`. -/

/-- `M^{⊗n} ≅ (L^∨)^{⊗n}` (`moduleNegativePower L.toModules n = moduleTensorPower (moduleSheafDual L) n`, defined by
recursion multiplying on the left). Induction on `n`: `n = 0` is `𝟙_ = O` (`unit_eq_tensorUnit`); for `n + 1`,
`M^{⊗n} ⊗ M ≅ (L^∨)^{⊗n} ⊗ L^∨` (the inductive isomorphism `⊗` `M = Modules.tensor L^∨ O ≅ L^∨ ⊗ 𝟙_ ≅ L^∨`), then
reorder with the braiding and return to `Modules.tensor` with `tensorIsoTensorObj`. -/
theorem truncatedJetAlgebra.piece_iso_negativePower {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (n : ℕ) :
    Nonempty (truncatedJetAlgebra.piece L n ≅ AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules n) := by
  induction n with
  | zero =>
    exact ⟨CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit Ct.toScheme).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    let D : Ct.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.moduleSheafDual L.toModules
    let eM : (L.zpow (-1)).toModules ≅ D :=
      AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj D (SheafOfModules.unit Ct.toScheme.ringCatSheaf) ≪≫
        CategoryTheory.MonoidalCategory.whiskerLeftIso D
          (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit Ct.toScheme)) ≪≫
        ρ_ D
    exact ⟨CategoryTheory.MonoidalCategory.tensorIso e eM ≪≫
      β_ (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules n) D ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj D (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules n)).symm⟩

/-- `(L.zpow (-n)).toModules` is `moduleNegativePower L.toModules n` (for `n = 0` both sides are `O`, `rfl`). -/
theorem LineBundle.zpow_neg_natCast_toModules {k : Type u} [Field k] {X : Variety k}
    (L : LineBundle X) (n : ℕ) :
    (L.zpow (-(n : ℤ))).toModules = AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules n := by
  cases n <;> rfl

/-- The underlying sheaf of modules is `⊕_{q ≤ κ} L^{-q}`: piecewise `piece_iso_negativePower`, then `biproduct.mapIso`. -/
theorem truncatedJetAlgebra_carrier {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    Nonempty ((truncatedJetAlgebra L κ).carrier ≅
      CategoryTheory.Limits.biproduct (fun q : Fin (κ + 1) => (L.zpow (-(q : ℤ))).toModules)) := by
  have e : ∀ q : Fin (κ + 1), truncatedJetAlgebra.piece L q ≅ (L.zpow (-(q : ℤ))).toModules := fun q =>
    (truncatedJetAlgebra.piece_iso_negativePower L q).some ≪≫
      CategoryTheory.eqToIso (LineBundle.zpow_neg_natCast_toModules L q).symm
  exact ⟨CategoryTheory.Limits.biproduct.mapIso e⟩

end
