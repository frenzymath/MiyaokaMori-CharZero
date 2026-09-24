import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyLocalRingHom

/-! # Universal property of the projective bundle: the image of the irrelevant ideal

Companion of `ProjectiveBundleUniversalProperty.lean` for (3/6) `localRingHom_map_irrelevant`.
Source: Stacks 01O4 (`lemma-apply-relative`, the representability direction: `ψ`
surjective in degree one ⟹ the morphism to `Proj` is everywhere defined).

Route:

* **Degree-one component is an epimorphism**: `Φ₁ = localRingHomSheafHom … 1 : g^*S₁ ⟶ O_V` is a composite of
  isomorphisms and of `ι^*(symGradedPullbackDesc f ψ 1)`, and `symPowPullbackDesc f ψ 1` is epi because
  `f^*(symPowπ 1) ≫ symPowPullbackDesc 1 = pullbackMonoidalPow 1 ≫ (𝟙_ ◁ ψ)` and `𝟙_ ◁ ψ` is conjugate to `ψ`
  by the left unitors (`epi_whiskerLeft_unit`). So `Sym¹ W ≅ W` is not needed.
* **Stalk generation** (`stalk_eq_smul_germ_of_isQuasicoherent`): for a quasi-coherent `H` on an affine open
  `W ∋ x`, every germ at `x` is `c • germ(t)` with `t ∈ Γ(W, H)` (shrink to a basic open `D(h) ∋ x`,
  `h^n • s = t|_{D(h)}`, invert `germ h`).
* **Pullback stalks** (`pullbackStalk_span_unit_germ_eq_top`): `(g^*H)_y` is spanned over `O_{Y,y}` by the germs of
  the adjunction-unit sections `η(t)|_⊤`, `t ∈ Γ(W, H)` (`modulePullbackStalkTensorMap_bijective` +
  the previous item, the unit is semilinear).
* **Epi onto `O_Y` gives a unit at every point** (`exists_mem_basicOpen_of_epi`): `Φ` epi ⟹ stalkwise surjective
  (`stalkMap_surjective_of_epi`); the germ of `1` is hit by some `z`, which lies in the span
  above; if all `φ(t) := Φ(η(t)|_⊤)` were non-units at `y`, `Submodule.span_induction` would put the image of `z` in
  `𝔪_y • germ(1)`, so `(1 - c) • germ(1) = 0` with `c ∈ 𝔪_y`; `smul_germ_one_eq_zero` gives `1 = c`, contradiction.
* **Affine schemes** (`ideal_eq_top_of_forall_exists_mem_basicOpen`): an ideal of `Γ(Y, O)` with no common zero is
  the unit ideal (`Ideal.exists_le_maximal`, points of `Y ≅ Spec Γ(Y, O)` are primes,
  `Scheme.map_PrimeSpectrum_basicOpen_of_affine`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.projBundle

/-! ## Monoidal / categorical pieces: the degree-one component is an epimorphism -/

section EpiPieces

set_option backward.isDefEq.respectTransparency.types false

/-- `𝟙_ C ◁ ψ` is epi when `ψ` is: it is conjugate to `ψ` by the left unitors. -/
theorem epi_whiskerLeft_unit {C : Type u} [Category.{v} C] [MonoidalCategory C] {A B : C} (ψ : A ⟶ B) [Epi ψ] :
    Epi (MonoidalCategoryStruct.whiskerLeft (𝟙_ C) ψ) := by
  have h : MonoidalCategoryStruct.whiskerLeft (𝟙_ C) ψ = ((λ_ A).hom ≫ ψ) ≫ (λ_ B).inv := by
    rw [← MonoidalCategory.leftUnitor_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- Generic shape of the composite `Φ₁`: (iso) ≫ (epi) ≫ (iso) ≫ (iso) ≫ (iso) is epi. Stated with explicit
hypotheses so that it can be applied by `exact` (the category instances carried by `≫` in definition bodies and in
statements differ syntactically, which makes instance chaining fail). -/
theorem epi_comp_five {C : Type u} [Category.{v} C] {A B D E F G : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (ha : IsIso a) (hb : Epi b) (hc : IsIso c) (hd : IsIso d) (he : IsIso e) :
    Epi (a ≫ b ≫ c ≫ d ≫ e) := by
  have := ha; have := hb; have := hc; have := hd; have := he
  infer_instance

/-- `pullbackMonoidalPow g W 1` is an isomorphism (`pullbackTensorObjHom` is an isomorphism, whiskered with
`pullbackUnitIso`). -/
theorem pullbackMonoidalPow_one_isIso {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) (W : X.Modules) :
    IsIso (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow g W 1) := by
  show IsIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g
    (AlgebraicGeometry.Scheme.Modules.monoidalPow W 0) W ≫
    MonoidalCategoryStruct.whiskerRight (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom _)
  exact (asIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g
    (AlgebraicGeometry.Scheme.Modules.monoidalPow W 0) W) ≪≫
    MonoidalCategory.whiskerRightIso (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g) _).isIso_hom

/-- `symPowPullbackDesc g ψ 1` is an epimorphism when `ψ` is:
`g^*(symPowπ W 1) ≫ symPowPullbackDesc g ψ 1 = pullbackMonoidalPow g W 1 ≫ (𝟙 ⊗ₘ ψ)`, the right side is
(iso) ≫ (epi). -/
theorem symPowPullbackDesc_one_epi {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) (W : X.Modules)
    {M : T.Modules} [M.IsLineBundle] (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj W ⟶ M) [Epi ψ] :
    Epi (AlgebraicGeometry.Scheme.Modules.symPowPullbackDesc g ψ 1) := by
  have h := AlgebraicGeometry.Scheme.Modules.pullback_map_symPowπ_comp_symPowPullbackDesc g W ψ 1
  have e1 : IsIso (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow g W 1) := pullbackMonoidalPow_one_isIso g W
  have e2 : Epi (AlgebraicGeometry.Scheme.Modules.monoidalPowMap ψ 1) := by
    show Epi (MonoidalCategoryStruct.tensorHom (𝟙 (𝟙_ T.Modules)) ψ)
    rw [MonoidalCategory.id_tensorHom]
    exact epi_whiskerLeft_unit ψ
  have : Epi (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow g W 1 ≫
      AlgebraicGeometry.Scheme.Modules.monoidalPowMap ψ 1) :=
    @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ e1) _ e2
  rw [← h] at this
  exact @epi_of_epi _ _ _ _ _ _ _ this

private theorem symGradedPullbackDesc_one_epi_aux {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj W ⟶ M) [Epi ψ]
    (S : X.GradedQCAlgebra) (hS : S = AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W hq)
    (D : (AlgebraicGeometry.Scheme.Modules.pullback g).obj (S.part 1) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow M 1)
    (hD : HEq D (AlgebraicGeometry.Scheme.Modules.symPowPullbackDesc g ψ 1)) : Epi D := by
  subst hS
  have hD' : D = AlgebraicGeometry.Scheme.Modules.symPowPullbackDesc g ψ 1 := eq_of_heq hD
  rw [hD']
  exact symPowPullbackDesc_one_epi g W ψ

/-- `symGradedPullbackDesc g ψ 1` is an epimorphism when `W` is quasi-coherent and `ψ` is epi. -/
theorem symGradedPullbackDesc_one_epi {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj W ⟶ M) [Epi ψ] :
    Epi (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc g ψ 1) := by
  have hS : AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W hq := by
    delta AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    exact dif_pos hq
  exact symGradedPullbackDesc_one_epi_aux g W hq ψ _ hS _
    (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc_heq_of_isQuasicoherent g hq ψ 1)

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- **The degree-one component `Φ₁ : g^*S₁ ⟶ O_V` of the local piece is an epimorphism.**
All factors of `localRingHomSheafHom … 1` are isomorphisms except `ι^*(symGradedPullbackDesc f ψ 1)`, which is
the pullback (a left adjoint, so epi-preserving) of an epimorphism (`symGradedPullbackDesc_one_epi`). -/
theorem localRingHomSheafHom_one_epi (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [Epi ψ] (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    Epi (localRingHomSheafHom V f M ψ U e W 1) := by
  have hq : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent := by
    have := AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
    exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  have hB : Epi (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc f ψ 1) :=
    symGradedPullbackDesc_one_epi f (AlgebraicGeometry.Scheme.Modules.dual V) hq ψ
  have e4 : IsIso (AlgebraicGeometry.Scheme.Modules.monoidalPowMap (localRingHomTriv f M U e W).hom 1) := by
    show IsIso (MonoidalCategoryStruct.tensorHom (𝟙 (𝟙_ _)) (localRingHomTriv f M U e W).hom)
    exact (MonoidalCategory.tensorIso (Iso.refl _) (localRingHomTriv f M U e W)).isIso_hom
  have e5 : IsIso (AlgebraicGeometry.Scheme.Modules.unitPowCollapse (U ⊓ f ⁻¹ᵁ W).toScheme 1) := by
    show IsIso (MonoidalCategoryStruct.whiskerRight (𝟙 (𝟙_ _)) (𝟙_ _) ≫ (λ_ (𝟙_ _)).hom)
    exact (MonoidalCategory.whiskerRightIso (Iso.refl _) _ ≪≫ λ_ _).isIso_hom
  unfold localRingHomSheafHom
  exact epi_comp_five _ _ _ _ _
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp (localRingHomIncl f U W) f).symm.app _).isIso_hom
    ((AlgebraicGeometry.Scheme.Modules.pullback (localRingHomIncl f U W)).map_epi _)
    (pullbackMonoidalPow_one_isIso (localRingHomIncl f U W) M) e4 e5

end EpiPieces

/-! ## Stalk generation for quasi-coherent sheaves and their pullbacks -/

section StalkGeneration

set_option backward.isDefEq.respectTransparency.types false

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Quasi-coherent sheaves are generated by their sections over an affine open, stalkwise**: for `H`
quasi-coherent, `W` affine, `x ∈ W`, every germ `m ∈ H_x` is `c • germ_x(t)` for some `t ∈ Γ(W, H)` and
`c ∈ O_{X,x}`. Proof: `m = germ(s₀)` with `s₀` on some `U ⊆ W`; pick a basic open `D(h) ⊆ U` with `x ∈ D(h)`
(`IsAffineOpen.exists_basicOpen_le`); quasi-coherent localization gives `t ∈ Γ(W, H)` and `n` with
`t|_{D(h)} = h^n • s₀|_{D(h)}`; `germ h` is a unit at `x`, so `m = (germ h)^{-n} • germ t`. -/
theorem stalk_eq_smul_germ_of_isQuasicoherent (H : X.Modules) [H.IsQuasicoherent] {W : X.Opens}
    (hW : AlgebraicGeometry.IsAffineOpen W) (x : X) (hx : x ∈ W) (m : H.presheaf.stalk x) :
    ∃ (c : X.presheaf.stalk x) (t : Γ(H, W)), m = c • H.presheaf.germ W x hx t := by
  obtain ⟨U, hUW, hxU, s₀, rfl⟩ := H.presheaf.exists_le_germ_eq m hx
  obtain ⟨h, hhU, hxh⟩ := hW.exists_basicOpen_le ⟨x, hxU⟩ hx
  obtain ⟨n, t, ht⟩ := AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map_basicOpen H hW h
    (H.presheaf.map (homOfLE hhU).op s₀)
  have hu : IsUnit (X.presheaf.germ W x hx h) := (X.mem_basicOpen h x hx).mp hxh
  refine ⟨((hu.unit⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x), t, ?_⟩
  have h1 : H.presheaf.germ W x hx t =
      (X.presheaf.germ W x hx h) ^ n • H.presheaf.germ U x hxU s₀ := by
    rw [← H.presheaf.germ_res_apply (homOfLE (X.basicOpen_le h)) x hxh t, ht,
      MiyaokaMori.FreeStalk.germ_smul', map_pow, X.presheaf.germ_res_apply,
      H.presheaf.germ_res_apply]
  have hinv : ((hu.unit⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) *
      ((hu.unit : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) ^ n = 1 := by
    rw [inv_pow, ← Units.val_pow_eq_pow_val, Units.inv_mul]
  rw [hu.unit_spec] at hinv
  rw [h1, smul_smul, hinv, one_smul]

/-- **Pullback stalks are spanned by the unit sections**: for `g : Y ⟶ X` landing in an affine open `W`
(`⊤ ≤ g⁻¹W`), `H` quasi-coherent on `X`, the stalk `(g^*H)_y` is spanned over `O_{Y,y}` by the germs of the
sections `η(t)|_⊤` (`η` the unit of `g^* ⊣ g_*`, `t ∈ Γ(W, H)`).
Proof: `modulePullbackStalkTensorMap` is surjective (`modulePullbackStalkTensorMap_bijective`), so `z` is a
sum of `a • unit(m)`; by `stalk_eq_smul_germ_of_isQuasicoherent`, `m = c • germ t`; the unit is semilinear and
`unit(germ t) = germ(η t)` (`modulePullbackStalkUnitAddHom_germ`). -/
theorem pullbackStalk_span_unit_germ_eq_top {Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X) (H : X.Modules)
    [H.IsQuasicoherent] {W : X.Opens} (hW : AlgebraicGeometry.IsAffineOpen W)
    (hle : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ W) (y : Y) :
    Submodule.span (Y.presheaf.stalk y) (Set.range fun t : Γ(H, W) =>
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.germ ⊤ y trivial
        (((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.map (homOfLE hle).op
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app H).val.app
            (op W)).hom t))) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hgy : g y ∈ W := hle (trivial : y ∈ (⊤ : Y.Opens))
  obtain ⟨t, rfl⟩ := (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective g H y).2 z
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a m =>
    obtain ⟨c, s, rfl⟩ := stalk_eq_smul_germ_of_isQuasicoherent H hW (g y) hgy m
    rw [AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap_tmul, map_smulₛₗ]
    have hg : AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g H y (H.presheaf.germ W (g y) hgy s) =
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.germ ⊤ y trivial
          (((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.map (homOfLE hle).op
            ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app H).val.app
              (op W)).hom s)) := by
      rw [TopCat.Presheaf.germ_res_apply]
      exact AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ g H y W hgy s
    rw [hg, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw

/-- **An epimorphism `Φ : g^*H ⟶ O_Y` produces, at every point, a section `φ(t) := Φ(η(t)|_⊤)` that is a unit
there** (`H` quasi-coherent, `g` landing in the affine open `W`).
Proof: `Φ` epi ⟹ surjective on stalks (`stalkMap_surjective_of_epi`), so the germ of `1` is `Φ_y(z)`; `z` lies in
the span of the germs of the `η(t)|_⊤` (`pullbackStalk_span_unit_germ_eq_top`). If no `φ(t)` were a unit at `y`,
`Submodule.span_induction` would give `Φ_y(z) = c • germ(1)` with `c ∈ 𝔪_y`, hence `(1 - c) • germ(1) = 0`, so
`1 = c` by `smul_germ_one_eq_zero` — impossible in a local ring. -/
theorem exists_mem_basicOpen_of_epi {Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X) (H : X.Modules)
    [H.IsQuasicoherent] {W : X.Opens} (hW : AlgebraicGeometry.IsAffineOpen W)
    (hle : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ W)
    (Φ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj H ⟶ SheafOfModules.unit Y.ringCatSheaf) [Epi Φ]
    (y : Y) :
    ∃ t : Γ(H, W), y ∈ Y.basicOpen ((Φ.val.app (op ⊤)).hom
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.map (homOfLE hle).op
        ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app H).val.app
          (op W)).hom t))) := by
  by_contra hcon
  simp only [not_exists] at hcon
  -- the images are all non-units at `y`
  have hnu : ∀ t : Γ(H, W), Y.presheaf.germ ⊤ y trivial ((Φ.val.app (op ⊤)).hom
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.map (homOfLE hle).op
        ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app H).val.app
          (op W)).hom t))) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := fun t =>
    (IsLocalRing.mem_maximalIdeal _).2 (fun hu => hcon t ((Y.mem_basicOpen_top _ y).2 hu))
  set one_g := (AlgebraicGeometry.Scheme.Modules.unitModule Y).presheaf.germ ⊤ y trivial (MiyaokaMori.FreeStalk.uSec ⊤ 1)
    with hone_g
  obtain ⟨z, hz⟩ := MiyaokaMori.FreeStalk.stalkMap_surjective_of_epi Φ y one_g
  have hspan := pullbackStalk_span_unit_germ_eq_top g H hW hle y
  have key : ∀ z ∈ Submodule.span (Y.presheaf.stalk y) (Set.range fun t : Γ(H, W) =>
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.germ ⊤ y trivial
        (((AlgebraicGeometry.Scheme.Modules.pullback g).obj H).presheaf.map (homOfLE hle).op
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app H).val.app
            (op W)).hom t))),
      ∃ c ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
        AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y Φ z = c • one_g := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨t, rfl⟩ := hz
      refine ⟨_, hnu t, ?_⟩
      rw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ]
      show (AlgebraicGeometry.Scheme.Modules.unitModule Y).presheaf.germ ⊤ y trivial (MiyaokaMori.FreeStalk.uSec ⊤ _) = _
      rw [MiyaokaMori.FreeStalk.uSec_eq_smul, MiyaokaMori.FreeStalk.germ_smul']
      rfl
    | zero => exact ⟨0, Submodule.zero_mem _, by rw [map_zero, zero_smul]⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc, hc'⟩ := ha
      obtain ⟨d, hd, hd'⟩ := hb
      exact ⟨c + d, Submodule.add_mem _ hc hd, by rw [map_add, hc', hd', add_smul]⟩
    | smul a z _ hz =>
      obtain ⟨c, hc, hc'⟩ := hz
      exact ⟨a * c, Ideal.mul_mem_left _ a hc, by rw [map_smul, hc', smul_smul]⟩
  obtain ⟨c, hc, hc'⟩ := key z (hspan ▸ Submodule.mem_top)
  rw [hz] at hc'
  have h0 : (1 - c) • one_g = 0 := by rw [sub_smul, one_smul, ← hc', sub_self]
  have h1 : (1 : Y.presheaf.stalk y) = c := sub_eq_zero.mp (MiyaokaMori.FreeStalk.smul_germ_one_eq_zero y _ h0)
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top (h1 ▸ hc)

end StalkGeneration

/-! ## Affine schemes: an ideal with no common zero is the unit ideal -/

section AffineIdeal

/-- On an affine scheme `Y`, an ideal `I ⊆ Γ(Y, O)` such that every point lies in `D(r)` for some `r ∈ I` is `⊤`.
Proof: otherwise `I ≤ 𝔪` maximal; `𝔪` is a point `p` of `Spec Γ(Y, O) ≅ Y`; the `r ∈ I` with `p ∈ D(r)` satisfies
`r ∉ 𝔪` (`Scheme.map_PrimeSpectrum_basicOpen_of_affine`, `PrimeSpectrum.mem_basicOpen`), contradiction. -/
theorem ideal_eq_top_of_forall_exists_mem_basicOpen (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (I : Ideal Γ(Y, ⊤)) (h : ∀ y : Y, ∃ r ∈ I, y ∈ Y.basicOpen r) : I = ⊤ := by
  by_contra hI
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  let p : Spec Γ(Y, ⊤) := ⟨m, hm.isPrime⟩
  obtain ⟨r, hrI, hyr⟩ := h (Y.isoSpec.inv p)
  have h1 : Y.isoSpec.inv p ∈ Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
    rw [AlgebraicGeometry.Scheme.map_PrimeSpectrum_basicOpen_of_affine]
    exact hyr
  have h2 : Y.isoSpec.hom (Y.isoSpec.inv p) = p := by
    show (Y.isoSpec.inv ≫ Y.isoSpec.hom) p = p
    rw [Iso.inv_hom_id]
    rfl
  have h3 : p ∈ PrimeSpectrum.basicOpen r := by
    have : Y.isoSpec.hom (Y.isoSpec.inv p) ∈ PrimeSpectrum.basicOpen r := h1
    rwa [h2] at this
  exact (PrimeSpectrum.mem_basicOpen _ _).mp h3 (hIm hrI)

end AffineIdeal

end AlgebraicGeometry.Scheme.projBundle

end
