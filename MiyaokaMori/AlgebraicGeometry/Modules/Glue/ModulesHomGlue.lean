import MiyaokaMori.Prelude

/-! # Gluing morphisms of sheaves of modules sectionwise

Let `X` be a scheme, `{U_i}` an open cover (`⨆ U_i = ⊤`), and `M`, `N` sheaves of `O_X`-modules.
For `φ : M|_W ⟶ N|_W` and `V ≤ W` write `sectionMapOfRestrictHom φ V : Γ(M, V) ⟶ Γ(N, V)`
(restrict to `W.ι ''ᵁ W.ι ⁻¹ᵁ V = V`, apply `φ`, restrict back; same body as
`restrictSectionMap`, which lives downstream).

* `exists_hom_of_sectionMap_agree`: if `f_i : M|_{U_i} ⟶ N|_{U_i}` satisfy
  `sectionMapOfRestrictHom (f i) V = sectionMapOfRestrictHom (f j) V` for all `V ≤ U_i ⊓ U_j`,
  there is `g : M ⟶ N` with `g.app V = sectionMapOfRestrictHom (f i) V` for all `V ≤ U_i`;
* `restrict_map_eq_of_app_eq_sectionMap`: `g.app V = sectionMapOfRestrictHom φ V` for all
  `V ≤ W` implies `g|_W = φ`;
* `hom_ext_of_cover`: two morphisms `g g' : M ⟶ N` with equal restrictions to every `U_i` are
  equal;
* `sectionMapOfRestrictHom_eq_of_app_eq`: if the section maps of `ψ : M|_{V'} ⟶ N|_{V'}`
  (`V' ≤ W`) agree with those of `φ` (aligned via `eqToHom`), then
  `sectionMapOfRestrictHom ψ V = sectionMapOfRestrictHom φ V` for `V ≤ V'`.

Proof sketch: `sectionMapOfRestrictHom φ` is natural in `V` and `Γ(X, V)`-linear
(`smul_restrictAppIso_hom`, `Hom.app_smul`, `Modules.map_smul`). For existence, the opens
contained in some `U_i` form a basis; the section maps define a natural transformation on this
basis, `TopCat.Sheaf.restrictHomEquivHom` extends it uniquely to a morphism of sheaves of abelian
groups, linearity is checked locally on the cover `{V ⊓ U_i}` using separatedness of `N`
(`TopCat.Sheaf.eq_of_locally_eq'`), and `PresheafOfModules.homMk` gives `g`. Uniqueness again
uses separatedness of `N`.

References: Stacks 04TN (gluing morphisms of sheaves); Mathlib `TopCat.Sheaf.restrictHomEquivHom`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X Y : AlgebraicGeometry.Scheme.{u}}


theorem glueAux_cat1 {C : Type*} [Category C] {A A' A1 A1' B1 B1' B B' : C}
    (m : A ⟶ A') (b' : A' ⟶ A1') (p' : A1' ⟶ B1') (c' : B1' ⟶ B')
    (b : A ⟶ A1) (p : A1 ⟶ B1) (c : B1 ⟶ B) (n : B ⟶ B') (o : A1 ⟶ A1') (o' : B1 ⟶ B1')
    (e1 : m ≫ b' = b ≫ o) (nat : o ≫ p' = p ≫ o') (e2 : o' ≫ c' = c ≫ n) :
    m ≫ (b' ≫ p' ≫ c') = (b ≫ p ≫ c) ≫ n := by
  rw [reassoc_of% e1, reassoc_of% nat, e2]; simp

theorem glueAux_cat2 {C : Type*} [Category C] {A A' B B' : C}
    (b : A ⟶ A') (a : A' ⟶ A) (p : A ⟶ B) (p' : A' ⟶ B') (c : B' ⟶ B)
    (e : b ≫ a = 𝟙 _) (nat : a ≫ p = p' ≫ c) : b ≫ p' ≫ c = p := by
  rw [← nat, reassoc_of% e]

theorem glueAux_cat4 {C : Type*} [Category C] {A A' A'' A1 B1 B B' B'' : C}
    (b' : A ⟶ A') (e1 : A' ⟶ A'') (p' : A'' ⟶ B'') (e2 : B'' ⟶ B') (c' : B' ⟶ B)
    (b : A ⟶ A1) (p : A1 ⟶ B1) (c : B1 ⟶ B) (o : A1 ⟶ A'') (o' : B1 ⟶ B'')
    (hx : b' ≫ e1 = b ≫ o) (nat : o ≫ p' = p ≫ o') (hy : o' ≫ e2 ≫ c' = c) :
    b' ≫ (e1 ≫ p' ≫ e2) ≫ c' = b ≫ p ≫ c := by
  rw [← hy, ← reassoc_of% nat, ← reassoc_of% hx]; simp

theorem glueAux_cat5 {C : Type*} [Category C] {A A1 A2 B2 B1 B : C}
    (x1 : A ⟶ A1) (x2 : A1 ⟶ A2) (p : A2 ⟶ B2) (y1 : B2 ⟶ B1) (y2 : B1 ⟶ B) (x : A ⟶ A2) (y : B2 ⟶ B)
    (hx : x1 ≫ x2 = x) (hy : y1 ≫ y2 = y) : x1 ≫ x2 ≫ p ≫ y1 ≫ y2 = x ≫ p ≫ y := by
  rw [← hx, ← hy]; simp

theorem glueAux_map2 {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a b c : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (k : a ⟶ c) : F.map f ≫ F.map g = F.map k := by
  rw [← F.map_comp]; congr 1
theorem glueAux_map3 {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a b c d : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (k : c ⟶ d) (l : a ⟶ d) : F.map f ≫ F.map g ≫ F.map k = F.map l := by
  rw [← F.map_comp, ← F.map_comp]; congr 1
theorem glueAux_map22 {T : Type*} [Preorder T] {C : Type*} [Category C] (F : Tᵒᵖ ⥤ C) {a b b' c : Tᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a ⟶ b') (g' : b' ⟶ c) : F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp]; congr 1

/-- Naturality of the section map in `V` (unfolded form; the two `≤` proofs used for restricting
back are parameters). -/
theorem sectionMapOfRestrictHom_naturality {M N : X.Modules} {W : X.Opens} (φ : M.restrict W.ι ⟶ N.restrict W.ι)
    (V V' : X.Opens) (hV' : V' ≤ V) (h1 : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V) (h2 : V' ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V') :
    M.presheaf.map (homOfLE hV').op ≫
      (M.presheaf.map (homOfLE (W.ι.image_preimage_le V')).op ≫ φ.app (W.ι ⁻¹ᵁ V') ≫
        N.presheaf.map (homOfLE h2).op) =
    (M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op ≫ φ.app (W.ι ⁻¹ᵁ V) ≫
        N.presheaf.map (homOfLE h1).op) ≫ N.presheaf.map (homOfLE hV').op := by
  have hle : W.ι ⁻¹ᵁ V' ≤ W.ι ⁻¹ᵁ V := fun x hx => hV' hx
  have nat := φ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  have e1 : M.presheaf.map (homOfLE hV').op ≫ M.presheaf.map (homOfLE (W.ι.image_preimage_le V')).op
      = M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op ≫
        M.presheaf.map (W.ι.opensFunctor.map (homOfLE hle)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  have e2 : N.presheaf.map (W.ι.opensFunctor.map (homOfLE hle)).op ≫ N.presheaf.map (homOfLE h2).op
      = N.presheaf.map (homOfLE h1).op ≫ N.presheaf.map (homOfLE hV').op := by
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  exact glueAux_cat1 _ _ _ _ _ _ _ _ _ _ e1 nat e2

theorem restrict_smul_eq (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) (W : Y.Opens)
    (r : Γ(X, f ''ᵁ W)) (x : Γ(M, f ''ᵁ W)) :
    (r • x : Γ(M, f ''ᵁ W)) = (((f.appIso W).hom r • (show Γ(M.restrict f, W) from x) : Γ(M.restrict f, W))) := by
  have := smul_restrictAppIso_hom_apply f M W ((f.appIso W).hom r) x
  simp at this
  exact this.symm

theorem restrict_hom_app_smul (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (φ : M.restrict f ⟶ N.restrict f) (W : Y.Opens)
    (r : Γ(X, f ''ᵁ W)) (x : Γ(M, f ''ᵁ W)) :
    (show Γ(N, f ''ᵁ W) from φ.app W (r • x : Γ(M, f ''ᵁ W))) = r • (show Γ(N, f ''ᵁ W) from φ.app W x) := by
  rw [restrict_smul_eq, restrict_smul_eq]
  exact Hom.app_smul φ _ _

/-- The section map `Γ(M, V) ⟶ Γ(N, V)` induced on `V ≤ W` by `φ : M|_W ⟶ N|_W`:
`Γ(M, V) → Γ(M, W.ι ''ᵁ W.ι ⁻¹ᵁ V) = Γ(M|_W, W.ι ⁻¹ᵁ V) →φ Γ(N|_W, W.ι ⁻¹ᵁ V) → Γ(N, V)`
(same body as `restrictSectionMap`, which lives downstream of this file). -/
def sectionMapOfRestrictHom {M N : X.Modules} {W : X.Opens} (φ : M.restrict W.ι ⟶ N.restrict W.ι) (V : X.Opens) (hV : V ≤ W) :
    Γ(M, V) ⟶ Γ(N, V) :=
  M.presheaf.map (CategoryTheory.homOfLE (W.ι.image_preimage_le V)).op ≫
    φ.app (W.ι ⁻¹ᵁ V) ≫
    N.presheaf.map (CategoryTheory.homOfLE (by
      rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
        AlgebraicGeometry.Scheme.Opens.opensRange_ι]
      exact le_inf hV le_rfl : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V)).op

theorem sectionMapOfRestrictHom_nat {M N : X.Modules} {W : X.Opens} (φ : M.restrict W.ι ⟶ N.restrict W.ι)
    (V V' : X.Opens) (hV : V ≤ W) (hV' : V' ≤ V) :
    M.presheaf.map (homOfLE hV').op ≫ sectionMapOfRestrictHom φ V' (hV'.trans hV) = sectionMapOfRestrictHom φ V hV ≫ N.presheaf.map (homOfLE hV').op :=
  sectionMapOfRestrictHom_naturality φ V V' hV' _ _

theorem sectionMapOfRestrictHom_smul {M N : X.Modules} {W : X.Opens} (φ : M.restrict W.ι ⟶ N.restrict W.ι)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V)) (x : Γ(M, V)) :
    sectionMapOfRestrictHom φ V hV (r • x) = r • sectionMapOfRestrictHom φ V hV x := by
  have h2 : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact le_inf hV le_rfl
  have hr : X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op r) = r := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : ((homOfLE (W.ι.image_preimage_le V)).op ≫ (homOfLE h2).op) = 𝟙 _ := rfl
    rw [this, X.presheaf.map_id]; rfl
  calc sectionMapOfRestrictHom φ V hV (r • x)
      = N.presheaf.map (homOfLE h2).op (show Γ(N, W.ι ''ᵁ W.ι ⁻¹ᵁ V) from φ.app (W.ι ⁻¹ᵁ V)
          (M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op (r • x))) := rfl
    _ = N.presheaf.map (homOfLE h2).op (show Γ(N, W.ι ''ᵁ W.ι ⁻¹ᵁ V) from φ.app (W.ι ⁻¹ᵁ V)
          (X.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op r •
            M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op x)) := by rw [map_smul]
    _ = N.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op r •
          (show Γ(N, W.ι ''ᵁ W.ι ⁻¹ᵁ V) from φ.app (W.ι ⁻¹ᵁ V)
            (M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op x))) := by
        rw [restrict_hom_app_smul]
    _ = r • sectionMapOfRestrictHom φ V hV x := by rw [map_smul, hr]; rfl

/-- Existence of glued morphisms (Stacks 04TN): morphisms on the pieces whose section maps agree on
overlaps glue to a global morphism. -/
theorem exists_hom_of_sectionMap_agree {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M N : X.Modules)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j), sectionMapOfRestrictHom (f i) V hi = sectionMapOfRestrictHom (f j) V hj) :
    ∃ g : M ⟶ N, ∀ i (V : X.Opens) (hV : V ≤ U i), g.app V = sectionMapOfRestrictHom (f i) V hV := by
  let B : { p : ι × X.Opens // p.2 ≤ U p.1 } → X.Opens := fun p => p.1.2
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro V x hx
    have hx' : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact ⟨V ⊓ U i, ⟨⟨(i, V ⊓ U i), inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  let α : (CategoryTheory.inducedFunctor B).op ⋙ M.presheaf ⟶
      (CategoryTheory.inducedFunctor B).op ⋙ N.presheaf :=
    { app := fun p => sectionMapOfRestrictHom (f p.unop.1.1) p.unop.1.2 p.unop.2
      naturality := by
        intro p q h
        have hle : q.unop.1.2 ≤ p.unop.1.2 := leOfHom h.unop.hom
        have := sectionMapOfRestrictHom_nat (f p.unop.1.1) p.unop.1.2 q.unop.1.2 p.unop.2 hle
        rw [hf p.unop.1.1 q.unop.1.1 q.unop.1.2 (hle.trans p.unop.2) q.unop.2] at this
        exact this }
  let φ : M.presheaf ⟶ N.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α
  have hφ : ∀ i (V : X.Opens) (hV : V ≤ U i), φ.app (op V) = sectionMapOfRestrictHom (f i) V hV := fun i V hV =>
    TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α ⟨(i, V), hV⟩
  have hlin : ∀ (V : X.Opens) (r : Γ(X, V)) (m : Γ(M, V)), φ.app (op V) (r • m) = r • φ.app (op V) m := by
    intro V r m
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i => V ⊓ U i) V
      (fun i => homOfLE inf_le_left) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
    · intro i
      have nat := fun y => ConcreteCategory.congr_hom (φ.naturality (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) y
      simp only [ConcreteCategory.comp_apply] at nat
      change N.presheaf.map _ (φ.app (op V) (r • m)) = N.presheaf.map _ (r • φ.app (op V) m)
      rw [← nat, map_smul, map_smul, ← nat, hφ i (V ⊓ U i) inf_le_right, sectionMapOfRestrictHom_smul]
  refine ⟨SheafOfModules.Hom.mk (PresheafOfModules.homMk φ (fun V r m => hlin V.unop r m)), ?_⟩
  intro i V hV
  rw [← hφ i V hV]
  rfl
theorem app_eq_sectionMap_restrict {M N : X.Modules} (g : M ⟶ N) {W : X.Opens} (V : X.Opens) (hV : V ≤ W) :
    g.app V = sectionMapOfRestrictHom ((restrictFunctor W.ι).map g) V hV := by
  have h2 : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact le_inf hV le_rfl
  have nat := g.mapPresheaf.naturality (homOfLE (W.ι.image_preimage_le V)).op
  simp only [mapPresheaf_app] at nat
  have e : N.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op ≫ N.presheaf.map (homOfLE h2).op = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact N.presheaf.map_id _
  change g.app V = M.presheaf.map _ ≫ g.app (W.ι ''ᵁ W.ι ⁻¹ᵁ V) ≫ N.presheaf.map _
  rw [reassoc_of% nat]
  erw [e]
  simp

theorem sectionMapOfRestrictHom_image {M N : X.Modules} {W : X.Opens} (φ : M.restrict W.ι ⟶ N.restrict W.ι)
    (W' : W.toScheme.Opens) (h : W.ι ''ᵁ W' ≤ W) :
    sectionMapOfRestrictHom φ (W.ι ''ᵁ W') h = φ.app W' := by
  have hle : W' ≤ W.ι ⁻¹ᵁ W.ι ''ᵁ W' := by rw [W.ι.preimage_image_eq]
  have nat := φ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  have e : M.presheaf.map (homOfLE (W.ι.image_preimage_le (W.ι ''ᵁ W'))).op ≫
      M.presheaf.map ((Hom.opensFunctor W.ι).map (homOfLE hle)).op = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact M.presheaf.map_id _
  exact glueAux_cat2 _ _ _ _ _ e nat

theorem restrict_map_eq_of_app_eq_sectionMap {M N : X.Modules} (g : M ⟶ N) {W : X.Opens}
    (φ : M.restrict W.ι ⟶ N.restrict W.ι) (h : ∀ (V : X.Opens) (hV : V ≤ W), g.app V = sectionMapOfRestrictHom φ V hV) :
    (restrictFunctor W.ι).map g = φ := by
  ext W'
  have hW' : W.ι ''ᵁ W' ≤ W := by
    conv_rhs => rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι W]
    exact AlgebraicGeometry.Scheme.Hom.image_le_opensRange _ _
  rw [← sectionMapOfRestrictHom_image φ W' hW', ← h]
  rfl
/-- Uniqueness of glued morphisms: two morphisms with equal restrictions to every piece of an open
cover are equal. -/
theorem hom_ext_of_cover {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) {M N : X.Modules}
    (g g' : M ⟶ N) (h : ∀ i, (restrictFunctor (U i).ι).map g = (restrictFunctor (U i).ι).map g') : g = g' := by
  ext V x
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i => V ⊓ U i) V
      (fun i => homOfLE inf_le_left) ?_ _ _ ?_
  · intro x hx
    have hx' : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · intro i
    have nat := fun y => ConcreteCategory.congr_hom (g.mapPresheaf.naturality (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) y
    have nat' := fun y => ConcreteCategory.congr_hom (g'.mapPresheaf.naturality (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) y
    simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at nat nat'
    change N.presheaf.map _ (g.app V x) = N.presheaf.map _ (g'.app V x)
    rw [← nat, ← nat', app_eq_sectionMap_restrict g (V ⊓ U i) inf_le_right,
      app_eq_sectionMap_restrict g' (V ⊓ U i) inf_le_right, h i]

theorem image_homOfLE_image {V' W : X.Opens} (h : V' ≤ W) (A : V'.toScheme.Opens) :
    W.ι ''ᵁ (X.homOfLE h ''ᵁ A) = V'.ι ''ᵁ A := by
  simp [← Scheme.Hom.comp_image]

theorem sectionMapOfRestrictHom_eq_of_app_eq {M N : X.Modules} {V' W : X.Opens} (h : V' ≤ W)
    (φ : M.restrict W.ι ⟶ N.restrict W.ι) (ψ : M.restrict V'.ι ⟶ N.restrict V'.ι)
    (hψ : ∀ A : V'.toScheme.Opens, ψ.app A =
      M.presheaf.map (eqToHom (image_homOfLE_image h A)).op ≫ φ.app (X.homOfLE h ''ᵁ A) ≫
        N.presheaf.map (eqToHom (image_homOfLE_image h A).symm).op)
    (V : X.Opens) (hV : V ≤ V') : sectionMapOfRestrictHom ψ V hV = sectionMapOfRestrictHom φ V (hV.trans h) := by
  have hle : X.homOfLE h ''ᵁ (V'.ι ⁻¹ᵁ V) ≤ W.ι ⁻¹ᵁ V := by
    rw [← Scheme.Hom.image_le_image_iff W.ι, image_homOfLE_image]
    refine (V'.ι.image_preimage_le V).trans ?_
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact le_inf (hV.trans h) le_rfl
  have nat := φ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  unfold sectionMapOfRestrictHom
  rw [hψ]
  exact glueAux_cat4 _ _ _ _ _ _ _ _ _ _ (glueAux_map22 M.presheaf _ _ _ _) nat (glueAux_map3 N.presheaf _ _ _ _)
end
end AlgebraicGeometry.Scheme.Modules
