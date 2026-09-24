import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso

/-! # Gluing module morphisms along a cover by open immersions

Statement: gluing of morphisms of `𝒪_X`-modules along a **family of open immersions**
`f i : Y i ⟶ X` whose images cover `X` (not necessarily of the form `U.ι` for opens `U`).
This is the sectionwise gluing lemma of `ModulesHomGlue` with `W.ι` replaced
by an arbitrary open immersion `f`; the proofs are the same (Stacks 04TN, Mathlib
`TopCat.Sheaf.restrictHomEquivHom`).

* `sectionMapOI f ρ V hV : Γ(M, V) ⟶ Γ(N, V)` for `ρ : M.restrict f ⟶ N.restrict f` and
  `V ≤ f.opensRange` (restrict to `f ''ᵁ f ⁻¹ᵁ V = V`, apply `ρ`, restrict back).
* `exists_hom_of_sectionMapOI_agree`: local morphisms agreeing on all opens of the overlaps glue.
* `exists_hom_of_restrict_compat`: the **locally directed** form used for chart covers: it suffices
  that the local morphisms are compatible along the designated transition maps `t : Y k ⟶ Y i`
  (a predicate `good i k t`; `t ≫ f i = f k`) in the sense
  `ρ k = κ.hom ≫ (restrictFunctor t).map (ρ i) ≫ κ.inv` (`κ = restrictCompIso`),
  provided any two pieces are, near each point of their overlap, refined by a common piece through
  designated transition maps.
* `isIso_of_restrict_isIso_cover`: a morphism that is an isomorphism after restriction to each
  piece is an isomorphism (stalks, `AlgebraicGeometry.Scheme.Modules.moduleStalkMap_bijective_of_restrict_isIso`).

Source: Stacks 04TN (gluing morphisms of sheaves), 01LI; Mathlib `TopCat.Sheaf.restrictHomEquivHom`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : AlgebraicGeometry.Scheme.{u}}

section SectionMap

variable {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion f]

theorem le_image_preimage_of_le_opensRange {V : X.Opens} (hV : V ≤ f.opensRange) :
    V ≤ f ''ᵁ f ⁻¹ᵁ V := by
  rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact le_inf hV le_rfl

variable {M N : X.Modules}

/-- The section map `Γ(M, V) ⟶ Γ(N, V)` induced on `V ≤ f.opensRange` by
`ρ : M.restrict f ⟶ N.restrict f`. -/
def sectionMapOI (ρ : M.restrict f ⟶ N.restrict f) (V : X.Opens) (hV : V ≤ f.opensRange) :
    Γ(M, V) ⟶ Γ(N, V) :=
  M.presheaf.map (homOfLE (f.image_preimage_le V)).op ≫ ρ.app (f ⁻¹ᵁ V) ≫
    N.presheaf.map (homOfLE (le_image_preimage_of_le_opensRange f hV)).op

theorem sectionMapOI_naturality (ρ : M.restrict f ⟶ N.restrict f)
    (V V' : X.Opens) (hV' : V' ≤ V) (h1 : V ≤ f ''ᵁ f ⁻¹ᵁ V) (h2 : V' ≤ f ''ᵁ f ⁻¹ᵁ V') :
    M.presheaf.map (homOfLE hV').op ≫
      (M.presheaf.map (homOfLE (f.image_preimage_le V')).op ≫ ρ.app (f ⁻¹ᵁ V') ≫
        N.presheaf.map (homOfLE h2).op) =
    (M.presheaf.map (homOfLE (f.image_preimage_le V)).op ≫ ρ.app (f ⁻¹ᵁ V) ≫
        N.presheaf.map (homOfLE h1).op) ≫ N.presheaf.map (homOfLE hV').op := by
  have hle : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V := fun x hx => hV' hx
  have nat := ρ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  have e1 : M.presheaf.map (homOfLE hV').op ≫ M.presheaf.map (homOfLE (f.image_preimage_le V')).op
      = M.presheaf.map (homOfLE (f.image_preimage_le V)).op ≫
        M.presheaf.map (f.opensFunctor.map (homOfLE hle)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  have e2 : N.presheaf.map (f.opensFunctor.map (homOfLE hle)).op ≫ N.presheaf.map (homOfLE h2).op
      = N.presheaf.map (homOfLE h1).op ≫ N.presheaf.map (homOfLE hV').op := by
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  exact glueAux_cat1 _ _ _ _ _ _ _ _ _ _ e1 nat e2

theorem sectionMapOI_nat (ρ : M.restrict f ⟶ N.restrict f) (V V' : X.Opens) (hV : V ≤ f.opensRange)
    (hV' : V' ≤ V) :
    M.presheaf.map (homOfLE hV').op ≫ sectionMapOI f ρ V' (hV'.trans hV) =
      sectionMapOI f ρ V hV ≫ N.presheaf.map (homOfLE hV').op :=
  sectionMapOI_naturality f ρ V V' hV' _ _

theorem sectionMapOI_smul (ρ : M.restrict f ⟶ N.restrict f) (V : X.Opens) (hV : V ≤ f.opensRange)
    (r : Γ(X, V)) (x : Γ(M, V)) :
    sectionMapOI f ρ V hV (r • x) = r • sectionMapOI f ρ V hV x := by
  have h2 : V ≤ f ''ᵁ f ⁻¹ᵁ V := le_image_preimage_of_le_opensRange f hV
  have hr : X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE (f.image_preimage_le V)).op r)
      = r := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : ((homOfLE (f.image_preimage_le V)).op ≫ (homOfLE h2).op) = 𝟙 _ := rfl
    rw [this, X.presheaf.map_id]; rfl
  calc sectionMapOI f ρ V hV (r • x)
      = N.presheaf.map (homOfLE h2).op (show Γ(N, f ''ᵁ f ⁻¹ᵁ V) from ρ.app (f ⁻¹ᵁ V)
          (M.presheaf.map (homOfLE (f.image_preimage_le V)).op (r • x))) := rfl
    _ = N.presheaf.map (homOfLE h2).op (show Γ(N, f ''ᵁ f ⁻¹ᵁ V) from ρ.app (f ⁻¹ᵁ V)
          (X.presheaf.map (homOfLE (f.image_preimage_le V)).op r •
            M.presheaf.map (homOfLE (f.image_preimage_le V)).op x)) := by rw [map_smul]
    _ = N.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE (f.image_preimage_le V)).op r •
          (show Γ(N, f ''ᵁ f ⁻¹ᵁ V) from ρ.app (f ⁻¹ᵁ V)
            (M.presheaf.map (homOfLE (f.image_preimage_le V)).op x))) := by
        rw [restrict_hom_app_smul]
    _ = r • sectionMapOI f ρ V hV x := by rw [map_smul, hr]; rfl

theorem app_eq_sectionMapOI_restrict (g : M ⟶ N) (V : X.Opens) (hV : V ≤ f.opensRange) :
    g.app V = sectionMapOI f ((restrictFunctor f).map g) V hV := by
  have h2 : V ≤ f ''ᵁ f ⁻¹ᵁ V := le_image_preimage_of_le_opensRange f hV
  have nat := g.mapPresheaf.naturality (homOfLE (f.image_preimage_le V)).op
  simp only [mapPresheaf_app] at nat
  have e : N.presheaf.map (homOfLE (f.image_preimage_le V)).op ≫ N.presheaf.map (homOfLE h2).op
      = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact N.presheaf.map_id _
  change g.app V = M.presheaf.map _ ≫ g.app (f ''ᵁ f ⁻¹ᵁ V) ≫ N.presheaf.map _
  rw [reassoc_of% nat]
  erw [e]
  simp

theorem sectionMapOI_image (ρ : M.restrict f ⟶ N.restrict f) (W : Y.Opens)
    (h : f ''ᵁ W ≤ f.opensRange) :
    sectionMapOI f ρ (f ''ᵁ W) h = ρ.app W := by
  have hle : W ≤ f ⁻¹ᵁ f ''ᵁ W := by rw [f.preimage_image_eq]
  have nat := ρ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  have e : M.presheaf.map (homOfLE (f.image_preimage_le (f ''ᵁ W))).op ≫
      M.presheaf.map (f.opensFunctor.map (homOfLE hle)).op = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact M.presheaf.map_id _
  exact glueAux_cat2 _ _ _ _ _ e nat

theorem restrict_map_eq_of_app_eq_sectionMapOI (g : M ⟶ N) (ρ : M.restrict f ⟶ N.restrict f)
    (h : ∀ (V : X.Opens) (hV : V ≤ f.opensRange), g.app V = sectionMapOI f ρ V hV) :
    (restrictFunctor f).map g = ρ := by
  ext W
  rw [← sectionMapOI_image f ρ W (f.image_le_opensRange W), ← h]
  rfl

end SectionMap

section Transition

variable {Y Z : AlgebraicGeometry.Scheme.{u}} (t : Z ⟶ Y) (f : Y ⟶ X) (f' : Z ⟶ X)
  [AlgebraicGeometry.IsOpenImmersion f] [AlgebraicGeometry.IsOpenImmersion f']

theorem opensRange_le_of_comp_eq (h : t ≫ f = f') : f'.opensRange ≤ f.opensRange := by
  rintro x ⟨y, rfl⟩
  refine ⟨t y, ?_⟩
  rw [← h]
  rfl

variable [AlgebraicGeometry.IsOpenImmersion t]

theorem image_eq_of_comp_eq (h : t ≫ f = f') (A : Z.Opens) : f' ''ᵁ A = f ''ᵁ (t ''ᵁ A) := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_image]
  subst h
  rfl

/-- `M.restrict f' ≅ (M.restrict f).restrict t` when `t ≫ f = f'`
(`restrictFunctorCongr` followed by `restrictFunctorComp`). -/
def restrictCompIso (h : t ≫ f = f') : restrictFunctor f' ≅ restrictFunctor f ⋙ restrictFunctor t :=
  restrictFunctorCongr h.symm ≪≫ restrictFunctorComp t f

theorem restrictCompIso_hom_app_app (h : t ≫ f = f') (M : X.Modules) (A : Z.Opens) :
    ((restrictCompIso t f f' h).hom.app M).app A =
      M.presheaf.map (eqToHom (image_eq_of_comp_eq t f f' h A).symm).op := by
  rw [restrictCompIso, Iso.trans_hom, NatTrans.comp_app, Hom.comp_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app]
  exact glueAux_map2 M.presheaf _ _ _

theorem restrictCompIso_inv_app_app (h : t ≫ f = f') (M : X.Modules) (A : Z.Opens) :
    ((restrictCompIso t f f' h).inv.app M).app A =
      M.presheaf.map (eqToHom (image_eq_of_comp_eq t f f' h A)).op := by
  rw [restrictCompIso, Iso.trans_inv, NatTrans.comp_app, Hom.comp_app,
    restrictFunctorCongr_inv_app_app, restrictFunctorComp_inv_app_app]
  exact glueAux_map2 M.presheaf _ _ _

variable {M N : X.Modules}

/-- The section maps of two local morphisms compatible along a transition `t` (with `t ≫ f = f'`)
agree on every open of the smaller piece. -/
theorem sectionMapOI_eq_of_transition (h : t ≫ f = f')
    (ρ : M.restrict f ⟶ N.restrict f) (ρ' : M.restrict f' ⟶ N.restrict f')
    (hρ : ∀ A : Z.Opens, ρ'.app A =
      M.presheaf.map (eqToHom (image_eq_of_comp_eq t f f' h A).symm).op ≫ ρ.app (t ''ᵁ A) ≫
        N.presheaf.map (eqToHom (image_eq_of_comp_eq t f f' h A)).op)
    (V : X.Opens) (hV : V ≤ f'.opensRange) :
    sectionMapOI f' ρ' V hV = sectionMapOI f ρ V (hV.trans (opensRange_le_of_comp_eq t f f' h)) := by
  have hle : t ''ᵁ (f' ⁻¹ᵁ V) ≤ f ⁻¹ᵁ V := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have : f' y ∈ V := hy
    rw [← h] at this
    exact this
  have nat := ρ.mapPresheaf.naturality (homOfLE hle).op
  simp only [mapPresheaf_app] at nat
  rw [restrict_map, restrict_map] at nat
  unfold sectionMapOI
  rw [hρ]
  exact glueAux_cat4 _ _ _ _ _ _ _ _ _ _ (glueAux_map22 M.presheaf _ _ _ _) nat
    (glueAux_map3 N.presheaf _ _ _ _)

end Transition

section Glue

variable {ι : Type u} (Y : ι → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, Y i ⟶ X)
  [∀ i, AlgebraicGeometry.IsOpenImmersion (f i)]

/-- Existence of a glued morphism (Stacks 04TN) for a family of open immersions covering `X`. -/
theorem exists_hom_of_sectionMapOI_agree (hcov : ∀ x : X, ∃ i, x ∈ (f i).opensRange)
    (M N : X.Modules) (ρ : ∀ i, M.restrict (f i) ⟶ N.restrict (f i))
    (hρ : ∀ i j (V : X.Opens) (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange),
      sectionMapOI (f i) (ρ i) V hi = sectionMapOI (f j) (ρ j) V hj) :
    ∃ g : M ⟶ N, ∀ i (V : X.Opens) (hV : V ≤ (f i).opensRange),
      g.app V = sectionMapOI (f i) (ρ i) V hV := by
  let B : { p : ι × X.Opens // p.2 ≤ (f p.1).opensRange } → X.Opens := fun p => p.1.2
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨V ⊓ (f i).opensRange, ⟨⟨(i, V ⊓ (f i).opensRange), inf_le_right⟩, rfl⟩, ⟨hx, hi⟩,
      inf_le_left⟩
  let α : (CategoryTheory.inducedFunctor B).op ⋙ M.presheaf ⟶
      (CategoryTheory.inducedFunctor B).op ⋙ N.presheaf :=
    { app := fun p => sectionMapOI (f p.unop.1.1) (ρ p.unop.1.1) p.unop.1.2 p.unop.2
      naturality := by
        intro p q h
        have hle : q.unop.1.2 ≤ p.unop.1.2 := leOfHom h.unop.hom
        have := sectionMapOI_nat (f p.unop.1.1) (ρ p.unop.1.1) p.unop.1.2 q.unop.1.2 p.unop.2 hle
        rw [hρ p.unop.1.1 q.unop.1.1 q.unop.1.2 (hle.trans p.unop.2) q.unop.2] at this
        exact this }
  let φ : M.presheaf ⟶ N.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α
  have hφ : ∀ i (V : X.Opens) (hV : V ≤ (f i).opensRange),
      φ.app (op V) = sectionMapOI (f i) (ρ i) V hV := fun i V hV =>
    TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α ⟨(i, V), hV⟩
  have hlin : ∀ (V : X.Opens) (r : Γ(X, V)) (m : Γ(M, V)),
      φ.app (op V) (r • m) = r • φ.app (op V) m := by
    intro V r m
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i => V ⊓ (f i).opensRange) V
      (fun i => homOfLE inf_le_left) ?_ _ _ ?_
    · intro x hx
      obtain ⟨i, hi⟩ := hcov x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
    · intro i
      have nat := fun y => ConcreteCategory.congr_hom
        (φ.naturality (homOfLE (inf_le_left : V ⊓ (f i).opensRange ≤ V)).op) y
      simp only [ConcreteCategory.comp_apply] at nat
      change N.presheaf.map _ (φ.app (op V) (r • m)) = N.presheaf.map _ (r • φ.app (op V) m)
      rw [← nat, map_smul, map_smul, ← nat, hφ i (V ⊓ (f i).opensRange) inf_le_right,
        sectionMapOI_smul]
  refine ⟨SheafOfModules.Hom.mk (PresheafOfModules.homMk φ (fun V r m => hlin V.unop r m)), ?_⟩
  intro i V hV
  rw [← hφ i V hV]
  rfl

/-- **Gluing along a locally directed family of open immersions.** Local morphisms
`ρ i : M.restrict (f i) ⟶ N.restrict (f i)` that are compatible along all transition maps
`t : Y k ⟶ Y i`, `t ≫ f i = f k` glue to a global morphism restricting to them, provided any two
pieces are refined near each point of their overlap by a common piece. -/
theorem exists_hom_of_restrict_compat (hcov : ∀ x : X, ∃ i, x ∈ (f i).opensRange)
    (good : ∀ i k, (Y k ⟶ Y i) → Prop)
    (hdir : ∀ i j (x : X), x ∈ (f i).opensRange → x ∈ (f j).opensRange →
      ∃ (k : ι) (ti : Y k ⟶ Y i) (tj : Y k ⟶ Y j),
        ti ≫ f i = f k ∧ tj ≫ f j = f k ∧ x ∈ (f k).opensRange ∧ good i k ti ∧ good j k tj)
    (M N : X.Modules) (ρ : ∀ i, M.restrict (f i) ⟶ N.restrict (f i))
    (hcompat : ∀ i k (t : Y k ⟶ Y i) [AlgebraicGeometry.IsOpenImmersion t], good i k t →
      ∀ (h : t ≫ f i = f k),
      ρ k = (restrictCompIso t (f i) (f k) h).hom.app M ≫ (restrictFunctor t).map (ρ i) ≫
        (restrictCompIso t (f i) (f k) h).inv.app N) :
    ∃ g : M ⟶ N, ∀ i, (restrictFunctor (f i)).map g = ρ i := by
  -- section maps agree along a transition
  have hsec : ∀ i k (t : Y k ⟶ Y i), good i k t → ∀ (h : t ≫ f i = f k) (V : X.Opens)
      (hV : V ≤ (f k).opensRange),
      sectionMapOI (f k) (ρ k) V hV =
        sectionMapOI (f i) (ρ i) V (hV.trans (opensRange_le_of_comp_eq t (f i) (f k) h)) := by
    intro i k t hg h V hV
    have : AlgebraicGeometry.IsOpenImmersion (t ≫ f i) := by rw [h]; infer_instance
    have : AlgebraicGeometry.IsOpenImmersion t :=
      AlgebraicGeometry.IsOpenImmersion.of_comp t (f i)
    refine sectionMapOI_eq_of_transition t (f i) (f k) h (ρ i) (ρ k) ?_ V hV
    intro A
    rw [hcompat i k t hg h, Hom.comp_app, Hom.comp_app, restrictCompIso_hom_app_app,
      restrictCompIso_inv_app_app]
    rfl
  -- agreement on every open of an overlap, by locality of equality in the sheaf `N`
  have hagree : ∀ i j (V : X.Opens) (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange),
      sectionMapOI (f i) (ρ i) V hi = sectionMapOI (f j) (ρ j) V hj := by
    intro i j V hi hj
    ext s
    choose k ti tj hti htj hk hgi hgj using hdir i j
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
      (fun x : { x : X // x ∈ V } => V ⊓ (f (k x.1 (hi x.2) (hj x.2))).opensRange) V
      (fun x => homOfLE inf_le_left) ?_ _ _ ?_
    · intro x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hk x (hi hx) (hj hx)⟩
    · intro x
      have e1 := ConcreteCategory.congr_hom (sectionMapOI_nat (f i) (ρ i) V
        (V ⊓ (f (k x.1 (hi x.2) (hj x.2))).opensRange) hi inf_le_left) s
      have e2 := ConcreteCategory.congr_hom (sectionMapOI_nat (f j) (ρ j) V
        (V ⊓ (f (k x.1 (hi x.2) (hj x.2))).opensRange) hj inf_le_left) s
      simp only [ConcreteCategory.comp_apply] at e1 e2
      rw [← e1, ← e2, ← hsec i _ (ti x.1 (hi x.2) (hj x.2)) (hgi x.1 (hi x.2) (hj x.2))
          (hti x.1 (hi x.2) (hj x.2)) _ inf_le_right,
        ← hsec j _ (tj x.1 (hi x.2) (hj x.2)) (hgj x.1 (hi x.2) (hj x.2))
          (htj x.1 (hi x.2) (hj x.2)) _ inf_le_right]
  obtain ⟨g, hg⟩ := exists_hom_of_sectionMapOI_agree Y f hcov M N ρ hagree
  exact ⟨g, fun i => restrict_map_eq_of_app_eq_sectionMapOI (f i) g (ρ i) (hg i)⟩

/-- A morphism of modules that is an isomorphism after restriction to each member of a family of
open immersions covering `X` is an isomorphism (stalks). -/
theorem isIso_of_restrict_isIso_cover (hcov : ∀ x : X, ∃ i, x ∈ (f i).opensRange)
    {M N : X.Modules} (g : M ⟶ N) (h : ∀ i, IsIso ((restrictFunctor (f i)).map g)) : IsIso g := by
  rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
  intro x
  obtain ⟨i, y, hy⟩ := hcov x
  have := h i
  have := AlgebraicGeometry.Scheme.Modules.moduleStalkMap_bijective_of_restrict_isIso (f i) g y
  rw [show (f i) y = x from hy] at this
  exact this

end Glue

end

end AlgebraicGeometry.Scheme.Modules
