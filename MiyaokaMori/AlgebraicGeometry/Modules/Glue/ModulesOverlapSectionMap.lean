import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue

/-! # Section maps of a morphism on an overlap

Let `X` be a scheme, `W ≤ W₁`, `W ≤ W₂` opens, `F₁`, `F₂` sheaves of modules on `W₁`, `W₂`, and
`θ : F₁|_W ⟶ F₂|_W`. For an open `V ≤ W` of `X` we define the section map
`overlapSectionMap θ V : Γ(F₁, W₁.ι ⁻¹ᵁ V) ⟶ Γ(F₂, W₂.ι ⁻¹ᵁ V)` (apply `θ.app (W.ι ⁻¹ᵁ V)` after
aligning via `(homOfLE) ''ᵁ (W.ι ⁻¹ᵁ V) = W_k.ι ⁻¹ᵁ V`). Then:

* `overlapSectionMap_naturality`: it is natural in `V` (commutes with the restriction maps of
  `F₁`, `F₂`);
* `app_eq_overlapSectionMap`: `θ.app A` equals `overlapSectionMap θ (W.ι ''ᵁ A)` composed on both
  sides with the aligning restriction maps;
* `overlapSectionMap_id`: for `θ = 𝟙`, `overlapSectionMap θ V = 𝟙`;
* `isIso_map_of_preimage_eq`: if `W₁.ι ⁻¹ᵁ V' = W₁.ι ⁻¹ᵁ V`, the restriction map
  `Γ(F₁, W₁.ι ⁻¹ᵁ V) ⟶ Γ(F₁, W₁.ι ⁻¹ᵁ V')` of `F₁` is an isomorphism.

The key identity of opens is `homOfLE_image_preimage`:
`(X.homOfLE h) ''ᵁ (V'.ι ⁻¹ᵁ V) = W.ι ⁻¹ᵁ V` for `V ≤ V' ≤ W` (both sides have image `V` under
`W.ι`, and `W.ι ''ᵁ ·` is injective). Naturality is the naturality of `θ` along
`W.ι ⁻¹ᵁ V' ≤ W.ι ⁻¹ᵁ V`; the remaining identities are compositions of images of a functor on a
poset, which depend only on the endpoints.

This formalizes "`φ_ij` acting on sections over opens inside `U_i ∩ U_j`" in the construction of
Stacks 00AL.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem homOfLE_image_preimage {V' W : X.Opens} (h : V' ≤ W) (V : X.Opens) (hV : V ≤ V') :
    X.homOfLE h ''ᵁ (V'.ι ⁻¹ᵁ V) = W.ι ⁻¹ᵁ V := by
  refine W.ι.image_injective ?_
  change W.ι ''ᵁ (X.homOfLE h ''ᵁ (V'.ι ⁻¹ᵁ V)) = W.ι ''ᵁ (W.ι ⁻¹ᵁ V)
  rw [image_homOfLE_image, AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.Scheme.Opens.opensRange_ι, AlgebraicGeometry.Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hV, inf_eq_right.mpr (hV.trans h)]

theorem glueAux_map_endo {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a : Tᵒᵖ}
    (f : a ⟶ a) : F.map f = 𝟙 _ := by
  rw [Subsingleton.elim f (𝟙 a), F.map_id]

theorem glueAux_map3_endo {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a b c : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (k : c ⟶ a) : (F.map f ≫ F.map g) ≫ F.map k = 𝟙 _ := by
  rw [← F.map_comp, ← F.map_comp]; exact glueAux_map_endo F _

theorem glueAux_map_id_map {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a b : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ a) : F.map f ≫ 𝟙 _ ≫ F.map g = 𝟙 _ := by
  rw [Category.id_comp, ← F.map_comp]; exact glueAux_map_endo F _

theorem glueAux_map2_endo {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a b : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ a) : F.map f ≫ F.map g = 𝟙 _ := by
  rw [← F.map_comp]; exact glueAux_map_endo F _

theorem glueAux_cat16 {C : Type*} [Category C] {A0 A1 A2 B0 B1 B2 P Q : C}
    (x1 : A0 ⟶ A1) (x2 : A1 ⟶ A2) (t : A2 ⟶ B0) (y1 : B0 ⟶ B1) (y2 : B1 ⟶ B2)
    (a : A2 ⟶ P) (o : P ⟶ Q) (b : Q ⟶ B0) (L : A0 ⟶ P) (R : Q ⟶ B2)
    (hθ : t = a ≫ o ≫ b) (hx : x1 ≫ x2 ≫ a = L) (hy : b ≫ y1 ≫ y2 = R) :
    x1 ≫ x2 ≫ t ≫ y1 ≫ y2 = L ≫ o ≫ R := by
  subst hθ hx hy; simp

theorem glueAux_cat17 {C : Type*} [Category C] {A P Q R B B' : C}
    (l : A ⟶ P) (o1 : P ⟶ Q) (m1 : Q ⟶ B) (m2 : B ⟶ Q) (o2 : Q ⟶ R) (r : R ⟶ B') (o3 : P ⟶ R)
    (l' : P ⟶ A) (r' : B' ⟶ R)
    (h : (l ≫ o1 ≫ m1) ≫ (m2 ≫ o2 ≫ r) = l ≫ o3 ≫ r) (hm : m1 ≫ m2 = 𝟙 _) (hl : l' ≫ l = 𝟙 _)
    (hr : r ≫ r' = 𝟙 _) : o1 ≫ o2 = o3 := by
  simp only [Category.assoc] at h
  rw [reassoc_of% hm] at h
  have h2 := congrArg (fun f => l' ≫ f ≫ r') h
  simp only [Category.assoc] at h2
  rw [reassoc_of% hl, reassoc_of% hl, hr] at h2
  simpa using h2

theorem glueAux_cat7 {C : Type*} [Category C] {A A0 A' B B' B0 : C}
    (b0 : A ⟶ A0) (b1 : A0 ⟶ A') (a : A' ⟶ A) (p : A ⟶ B) (p' : A' ⟶ B') (c1 : B' ⟶ B0) (c0 : B0 ⟶ B)
    (c : B' ⟶ B) (e : (b0 ≫ b1) ≫ a = 𝟙 _) (nat : a ≫ p = p' ≫ c) (hc : c1 ≫ c0 = c) :
    p = b0 ≫ (b1 ≫ p' ≫ c1) ≫ c0 := by
  simp only [Category.assoc] at e ⊢
  rw [hc, ← nat, reassoc_of% e]

variable {W W₁ W₂ : X.Opens} (h₁ : W ≤ W₁) (h₂ : W ≤ W₂)
  {F₁ : W₁.toScheme.Modules} {F₂ : W₂.toScheme.Modules}

/-- The section map of `θ : F₁|_W ⟶ F₂|_W` on an open `V ≤ W` of `X`. -/
def overlapSectionMap (θ : F₁.restrict (X.homOfLE h₁) ⟶ F₂.restrict (X.homOfLE h₂)) (V : X.Opens)
    (hV : V ≤ W) : Γ(F₁, W₁.ι ⁻¹ᵁ V) ⟶ Γ(F₂, W₂.ι ⁻¹ᵁ V) :=
  F₁.presheaf.map (eqToHom (homOfLE_image_preimage h₁ V hV)).op ≫ θ.app (W.ι ⁻¹ᵁ V) ≫
    F₂.presheaf.map (eqToHom (homOfLE_image_preimage h₂ V hV).symm).op

theorem overlapSectionMap_naturality (θ : F₁.restrict (X.homOfLE h₁) ⟶ F₂.restrict (X.homOfLE h₂))
    (V V' : X.Opens) (hV : V ≤ W) (hV' : V' ≤ V) :
    F₁.presheaf.map (homOfLE (W₁.ι.preimage_mono hV')).op ≫ overlapSectionMap h₁ h₂ θ V' (hV'.trans hV) =
      overlapSectionMap h₁ h₂ θ V hV ≫ F₂.presheaf.map (homOfLE (W₂.ι.preimage_mono hV')).op := by
  have hle : W.ι ⁻¹ᵁ V' ≤ W.ι ⁻¹ᵁ V := W.ι.preimage_mono hV'
  have nat := θ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  exact glueAux_cat1 _ _ _ _ _ _ _ _ _ _ (glueAux_map22 F₁.presheaf _ _ _ _) nat
    (glueAux_map22 F₂.presheaf _ _ _ _)

theorem preimage_image_eq_homOfLE_image (A : W.toScheme.Opens) {V : X.Opens} (hAV : W.ι ''ᵁ A = V) :
    W₁.ι ⁻¹ᵁ V = X.homOfLE h₁ ''ᵁ A := by
  subst hAV
  have hA : W.ι ''ᵁ A ≤ W := by
    conv_rhs => rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι W]
    exact AlgebraicGeometry.Scheme.Hom.image_le_opensRange _ _
  rw [← homOfLE_image_preimage h₁ _ hA, W.ι.preimage_image_eq]

theorem le_of_image_eq (A : W.toScheme.Opens) {V : X.Opens} (hAV : W.ι ''ᵁ A = V) : V ≤ W := by
  subst hAV
  conv_rhs => rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι W]
  exact AlgebraicGeometry.Scheme.Hom.image_le_opensRange _ _

theorem app_eq_overlapSectionMap (θ : F₁.restrict (X.homOfLE h₁) ⟶ F₂.restrict (X.homOfLE h₂))
    (A : W.toScheme.Opens) {V : X.Opens} (hAV : W.ι ''ᵁ A = V) :
    θ.app A = F₁.presheaf.map (eqToHom (preimage_image_eq_homOfLE_image h₁ A hAV)).op ≫
      overlapSectionMap h₁ h₂ θ V (le_of_image_eq A hAV) ≫
      F₂.presheaf.map (eqToHom (preimage_image_eq_homOfLE_image h₂ A hAV).symm).op := by
  subst hAV
  have hle : A ≤ W.ι ⁻¹ᵁ W.ι ''ᵁ A := by rw [W.ι.preimage_image_eq]
  have nat := θ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  exact glueAux_cat7 _ _ _ _ _ _ _ _ (glueAux_map3_endo F₁.presheaf _ _ _) nat (glueAux_map2 F₂.presheaf _ _ _)

theorem overlapSectionMap_id (F : W₁.toScheme.Modules) (V : X.Opens) (hV : V ≤ W) :
    overlapSectionMap h₁ h₁ (𝟙 (F.restrict (X.homOfLE h₁))) V hV = 𝟙 _ := by
  exact glueAux_map_id_map F.presheaf _ _

theorem isIso_map_of_preimage_eq (F : W₁.toScheme.Modules) {V V' : X.Opens}
    (h : W₁.ι ⁻¹ᵁ V' = W₁.ι ⁻¹ᵁ V) (f : op (W₁.ι ⁻¹ᵁ V) ⟶ op (W₁.ι ⁻¹ᵁ V')) :
    IsIso (F.presheaf.map f) := by
  have : IsIso f := ⟨⟨(eqToHom h.symm).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  infer_instance

end

end AlgebraicGeometry.Scheme.Modules
