import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleFrameChange
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyLocalRingHom
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyIrrelevant
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftLocalNaturality
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftDataOfEpi

/-! # Universal property of the projective bundle: pieces for the compatibility of the local lifts

Companion of `ProjectiveBundleUniversalProperty.lean` for (4/6) `liftLocal_compat`.
Source: Stacks 01O4 (`lemma-apply-relative`, "up to strict equivalence": changing the trivialization or the
affine chart changes the local ring map by a global unit / by restriction, which does not change the morphism to
`Proj`); 01NQ (gluing data of the relative Proj).

Contents:

* `toSpecAway`, `toSpecAway_comp_algebraMap`, `evalAway`, `toBasicOpenOfGlobalSections_eq'`,
  `basicOpen_ι_fromOfGlobalSections'`: Mathlib's `Proj.toBasicOpenOfGlobalSections` written as
  `D(x) → Spec Γ(Y)_x → Spec A_{(t)} ≅ D₊(t)`.
* `fromOfGlobalSections_precomp` (**naturality in the source**):
  `h ≫ fromOfGlobalSections 𝒜 f = fromOfGlobalSections 𝒜 (h^♯ ∘ f)`.
* `fromOfGlobalSections_comp_map` (**naturality in the graded ring**):
  `fromOfGlobalSections ℬ f ≫ Proj.map g = fromOfGlobalSections 𝒜 (f ∘ g)`.
* `hom_ext_of_forall_affine`: two morphisms out of an open subscheme agree if they agree on a family of affine
  opens covering it.
* `liftData`, `localRingHom_eq_liftLocalRingHomAux`: `projBundle.localRingHom` is the general local ring map
  `relativeProj.liftLocalRingHomAux` for the `LiftData` `Ψ_m := symGradedPullbackDesc f ψ m` (`rfl` on each
  graded piece).
* `exists_unit_localRingHom_restrict_scale` (the local ring map is compatible with restriction of the affine chart,
  up to the powers of a unit), `exists_unit_localRingHom_scale` (two trivializations change the local ring map by the
  powers of a unit): both from the general lemmas `liftLocalRingHomAux_comp/_restrict/_congr/_unit_scale`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.projBundle

/-! ## Mathlib's `Proj.fromOfGlobalSections` on basic opens -/

section ProjNaturality

variable {A : Type u} [CommRing A]

/-- The leg `D(x) ⟶ Spec Γ(Y, ⊤)_x` of Mathlib's `Proj.toBasicOpenOfGlobalSections`
(restriction of `Y.toSpecΓ` to the basic open, then `basicOpenIsoSpecAway`). -/
def toSpecAway (Y : AlgebraicGeometry.Scheme.{u}) (x : Γ(Y, ⊤)) :
    (Y.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  (Y.isoOfEq (Y.toSpecΓ_preimage_basicOpen x)).inv ≫
    Y.toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫ (AlgebraicGeometry.basicOpenIsoSpecAway x).hom

/-- `toSpecAway` followed by the localization map is `D(x).ι ≫ Y.toSpecΓ`; this characterizes it since
`Spec (Γ_x) → Spec Γ` is a monomorphism. -/
theorem toSpecAway_comp_algebraMap (Y : AlgebraicGeometry.Scheme.{u}) (x : Γ(Y, ⊤)) :
    toSpecAway Y x ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x))) =
      (Y.basicOpen x).ι ≫ Y.toSpecΓ := by
  simp only [toSpecAway, Category.assoc, AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap]
  rw [AlgebraicGeometry.morphismRestrict_ι Y.toSpecΓ (PrimeSpectrum.basicOpen x)]
  exact AlgebraicGeometry.Scheme.isoOfEq_inv_ι_assoc Y (Y.toSpecΓ_preimage_basicOpen x) Y.toSpecΓ

/-- `f : A →+* Γ(Y, ⊤)` extended to the localizations `A_t →+* Γ(Y, ⊤)_x` (`x = f t`); the same localization
map as in Mathlib's `Proj.toBasicOpenOfGlobalSections`. -/
def evalAway {Y : AlgebraicGeometry.Scheme.{u}} (f : A →+* Γ(Y, ⊤)) (t : A) {x : Γ(Y, ⊤)} (H : f t = x) :
    Localization.Away t →+* Localization.Away x :=
  IsLocalization.map (M := Submonoid.powers t) (T := Submonoid.powers x) (Localization.Away x) f (by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
    simp [H])

/-- `evalAway` restricted along a scheme morphism `h : Y' ⟶ Y` is `evalAway` of the composite
(`IsLocalization.map_comp_map`). -/
theorem awayMap_comp_evalAway {Y' Y : AlgebraicGeometry.Scheme.{u}} (h : Y' ⟶ Y) (f : A →+* Γ(Y, ⊤))
    (t : A) :
    (IsLocalization.Away.map (Localization.Away (f t)) (Localization.Away (h.appTop (f t)))
        h.appTop.hom (f t)).comp (evalAway f t rfl) =
      evalAway (h.appTop.hom.comp f) t (x := h.appTop (f t)) rfl :=
  IsLocalization.map_comp_map _ _

variable {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Mathlib's `Proj.toBasicOpenOfGlobalSections` as an explicit composite (definitional unfolding). -/
theorem toBasicOpenOfGlobalSections_eq' {Y : AlgebraicGeometry.Scheme.{u}} (f : A →+* Γ(Y, ⊤))
    {t : A} {x : Γ(Y, ⊤)} (H : f t = x) {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections 𝒜 f H hd ht =
      toSpecAway Y x ≫
        Spec.map (CommRingCat.ofHom ((evalAway f t H).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 t ht hd).inv := by
  simp only [AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections, toSpecAway, evalAway, Category.assoc]

/-- `D(x).ι ≫ fromOfGlobalSections f = toBasicOpenOfGlobalSections f ≫ D₊(t).ι` for `x = f t`
(`Proj.fromOfGlobalSections_resLE` + `resLE_comp_ι`). -/
theorem basicOpen_ι_fromOfGlobalSections' {Y : AlgebraicGeometry.Scheme.{u}} (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {t : A} {x : Γ(Y, ⊤)} (H : f t = x) {d : ℕ}
    (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    (Y.basicOpen x).ι ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf =
      AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections 𝒜 f H hd ht ≫
        (AlgebraicGeometry.Proj.basicOpen 𝒜 t).ι := by
  subst H
  rw [← AlgebraicGeometry.Proj.fromOfGlobalSections_resLE 𝒜 f hf hd ht]
  exact (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf)
    (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hd ht).ge).symm

/-- `fromOfGlobalSections` depends only on the ring map (the proof argument is irrelevant). -/
theorem fromOfGlobalSections_congr {Y : AlgebraicGeometry.Scheme.{u}} {f g : A →+* Γ(Y, ⊤)} (h : f = g)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf = AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 g hg := by
  subst h; rfl

/-- The irrelevant-ideal condition is preserved by postcomposition with `h^♯`. -/
theorem irrelevant_map_comp_appTop {Y' Y : AlgebraicGeometry.Scheme.{u}} (h : Y' ⟶ Y) (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (h.appTop.hom.comp f) = ⊤ := by
  rw [← Ideal.map_map, hf, Ideal.map_top]

/-- Naturality of `toSpecAway` in the scheme: for `h : Y' ⟶ Y` and `x ∈ Γ(Y, ⊤)`,
`h|_{D(h^♯ x)} ≫ toSpecAway Y x = toSpecAway Y' (h^♯ x) ≫ Spec (Γ(Y)_x → Γ(Y')_{h^♯ x})`.
Proof: both sides followed by the monomorphism `Spec Γ(Y)_x → Spec Γ(Y)` are `D(h^♯ x).ι ≫ h ≫ Y.toSpecΓ`
(`toSpecAway_comp_algebraMap`, `Scheme.toSpecΓ_naturality`, `IsLocalization.map_comp`). -/
theorem toSpecAway_naturality {Y' Y : AlgebraicGeometry.Scheme.{u}} (h : Y' ⟶ Y) (x : Γ(Y, ⊤)) :
    h.resLE (Y.basicOpen x) (Y'.basicOpen (h.appTop x)) (AlgebraicGeometry.Scheme.preimage_basicOpen_top h x).ge ≫
        toSpecAway Y x =
      toSpecAway Y' (h.appTop x) ≫
        Spec.map (CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away x)
          (Localization.Away (h.appTop x)) h.appTop.hom x)) := by
  apply (cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x))))).mp
  have hring : (IsLocalization.Away.map (Localization.Away x) (Localization.Away (h.appTop x))
        h.appTop.hom x).comp (algebraMap Γ(Y, ⊤) (Localization.Away x)) =
      (algebraMap Γ(Y', ⊤) (Localization.Away (h.appTop x))).comp h.appTop.hom :=
    IsLocalization.map_comp _
  have e1 : (h.resLE (Y.basicOpen x) (Y'.basicOpen (h.appTop x))
        (AlgebraicGeometry.Scheme.preimage_basicOpen_top h x).ge ≫ toSpecAway Y x) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x))) =
      (Y'.basicOpen (h.appTop x)).ι ≫ Y'.toSpecΓ ≫ Spec.map h.appTop := by
    rw [Category.assoc, toSpecAway_comp_algebraMap, ← Category.assoc,
      AlgebraicGeometry.Scheme.Hom.resLE_comp_ι, Category.assoc, AlgebraicGeometry.Scheme.toSpecΓ_naturality]
  have e2 : (toSpecAway Y' (h.appTop x) ≫
        Spec.map (CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away x)
          (Localization.Away (h.appTop x)) h.appTop.hom x))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x))) =
      (Y'.basicOpen (h.appTop x)).ι ≫ Y'.toSpecΓ ≫ Spec.map h.appTop := by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp,
      Spec.map_comp, ← Category.assoc, toSpecAway_comp_algebraMap, Category.assoc, CommRingCat.ofHom_hom]
  exact e1.trans e2.symm

/-- **Naturality of `Proj.fromOfGlobalSections` in the source** (Stacks 01O4: the functor `F₁` is a functor):
`h ≫ fromOfGlobalSections 𝒜 f = fromOfGlobalSections 𝒜 (h^♯ ∘ f)`.
Proof: check on the cover of `Y'` by the `D(h^♯(f t))`, `t` homogeneous of positive degree
(`Proj.openCoverOfMapIrrelevantEqTop`); on such a piece both sides are `toBasicOpenOfGlobalSections ≫ D₊(t).ι`
(`basicOpen_ι_fromOfGlobalSections'`), and these agree by `toSpecAway_naturality` and `awayMap_comp_evalAway`. -/
theorem fromOfGlobalSections_precomp {Y' Y : AlgebraicGeometry.Scheme.{u}} (h : Y' ⟶ Y) (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    h ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf =
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 (h.appTop.hom.comp f) (irrelevant_map_comp_appTop 𝒜 h f hf) := by
  refine (AlgebraicGeometry.Proj.openCoverOfMapIrrelevantEqTop 𝒜 (h.appTop.hom.comp f)
    (irrelevant_map_comp_appTop 𝒜 h f hf)).hom_ext _ _ fun ri ↦ ?_
  obtain ⟨d, t, hd, ht⟩ := ri
  change (Y'.basicOpen (h.appTop (f t))).ι ≫ h ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf =
    (Y'.basicOpen (h.appTop (f t))).ι ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 _ _
  rw [basicOpen_ι_fromOfGlobalSections' 𝒜 (h.appTop.hom.comp f) _ (x := h.appTop (f t)) rfl hd ht,
    ← Category.assoc,
    ← AlgebraicGeometry.Scheme.Hom.resLE_comp_ι h (AlgebraicGeometry.Scheme.preimage_basicOpen_top h (f t)).ge,
    Category.assoc, basicOpen_ι_fromOfGlobalSections' 𝒜 f hf rfl hd ht, ← Category.assoc,
    toBasicOpenOfGlobalSections_eq', toBasicOpenOfGlobalSections_eq', ← Category.assoc,
    toSpecAway_naturality h (f t)]
  have hring : (IsLocalization.Away.map (Localization.Away (f t)) (Localization.Away (h.appTop (f t)))
        h.appTop.hom (f t)).comp ((evalAway f t rfl).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t))) =
      (evalAway (h.appTop.hom.comp f) t (x := h.appTop (f t)) rfl).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)) := by
    rw [← RingHom.comp_assoc, awayMap_comp_evalAway]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hring]

variable {B : Type u} [CommRing B] {τ : Type u} [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ℕ → τ) [GradedRing ℬ]

/-- The irrelevant-ideal condition is preserved by precomposition with a graded ring map `g` with
`ℬ₊ ≤ 𝒜₊.map g`. -/
theorem irrelevant_map_comp_gradedRingHom (g : 𝒜 →+*ᵍ ℬ)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    {Y : AlgebraicGeometry.Scheme.{u}} (f : B →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp (g : A →+* B)) = ⊤ := by
  rw [eq_top_iff, ← hf, ← Ideal.map_map]
  exact Ideal.map_mono hg

/-- The ring identity behind `fromOfGlobalSections_comp_map`: on `A_{(t)}`, first mapping to `B_{(g t)}` and
then evaluating by `f` is evaluating by `f ∘ g` (check on `a / t^n`). -/
theorem evalAway_comp_awayMap (g : 𝒜 →+*ᵍ ℬ) {Y : AlgebraicGeometry.Scheme.{u}} (f : B →+* Γ(Y, ⊤))
    {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (H : (f.comp (g : A →+* B)) t = f (g t)) :
    ((evalAway f (g t) rfl).comp
        (algebraMap (HomogeneousLocalization.Away ℬ (g t)) (Localization.Away (g t)))).comp
      (HomogeneousLocalization.Away.map g t) =
    (evalAway (f.comp (g : A →+* B)) t H).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)) := by
  ext y
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ht y
  change evalAway f (g t) rfl (algebraMap (HomogeneousLocalization.Away ℬ (g t)) (Localization.Away (g t))
      (HomogeneousLocalization.Away.map g t (HomogeneousLocalization.Away.mk 𝒜 ht n a ha))) =
    evalAway (f.comp (g : A →+* B)) t H
      (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)
        (HomogeneousLocalization.Away.mk 𝒜 ht n a ha))
  rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  simp only [evalAway, Localization.mk_eq_mk', IsLocalization.map_mk', map_pow]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **Naturality of `Proj.fromOfGlobalSections` in the graded ring** (`Proj.map` functoriality):
`fromOfGlobalSections ℬ f ≫ Proj.map g = fromOfGlobalSections 𝒜 (f ∘ g)`.
Proof: check on the cover of `Y` by the `D(f (g t))`, `t ∈ 𝒜_d`, `d > 0`; on such a piece the left side is
`toBasicOpenOfGlobalSections ℬ f ≫ awayι ℬ (g t) ≫ Proj.map g = … ≫ Spec (Away.map g t) ≫ awayι 𝒜 t`
(`Proj.awayι_comp_map`) and the ring maps agree by `evalAway_comp_awayMap`. -/
theorem fromOfGlobalSections_comp_map (g : 𝒜 →+*ᵍ ℬ)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    {Y : AlgebraicGeometry.Scheme.{u}} (f : B →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections ℬ f hf ≫ AlgebraicGeometry.Proj.map g hg =
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 (f.comp (g : A →+* B))
        (irrelevant_map_comp_gradedRingHom 𝒜 ℬ g hg f hf) := by
  refine (AlgebraicGeometry.Proj.openCoverOfMapIrrelevantEqTop 𝒜 (f.comp (g : A →+* B))
    (irrelevant_map_comp_gradedRingHom 𝒜 ℬ g hg f hf)).hom_ext _ _ fun ri ↦ ?_
  obtain ⟨d, t, hd, ht⟩ := ri
  change (Y.basicOpen (f (g t))).ι ≫ AlgebraicGeometry.Proj.fromOfGlobalSections ℬ f hf ≫
      AlgebraicGeometry.Proj.map g hg =
    (Y.basicOpen (f (g t))).ι ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 _ _
  have H : (f.comp (g : A →+* B)) t = f (g t) := rfl
  rw [basicOpen_ι_fromOfGlobalSections' 𝒜 (f.comp (g : A →+* B)) _ H hd ht, ← Category.assoc,
    basicOpen_ι_fromOfGlobalSections' ℬ f hf (t := g t) (x := f (g t)) rfl hd (g.map_mem ht),
    toBasicOpenOfGlobalSections_eq',
    toBasicOpenOfGlobalSections_eq']
  simp only [Category.assoc, AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
  rw [AlgebraicGeometry.Proj.awayι_comp_map g hg hd t ht, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    evalAway_comp_awayMap 𝒜 ℬ g f ht H]

end ProjNaturality

/-! ## Checking equality of morphisms on a family of affine opens -/

section HomExt

/-- Two morphisms `a b : U ⟶ Z` out of an open subscheme `U ⊆ T` agree if they agree after restriction to a
family of affine opens `V ≤ U` of `T` (satisfying a side condition `P`) that covers `U`.
Proof: `Scheme.Cover.hom_ext` for the cover of `U` by the `U.ι ⁻¹ᵁ V`; the inclusion `(U.ι ⁻¹ᵁ V).ι` is
`(isoImage) ≫ (isoOfEq) ≫ T.homOfLE (V ≤ U)` (`Scheme.Hom.isoImage_hom_ι`, `U.ι ''ᵁ U.ι ⁻¹ᵁ V = V`). -/
theorem hom_ext_of_forall_affine {T : AlgebraicGeometry.Scheme.{u}} (U : T.Opens) {Z : AlgebraicGeometry.Scheme.{u}}
    (a b : U.toScheme ⟶ Z) (P : T.Opens → Prop)
    (hcov : ∀ t : U, ∃ V : T.Opens, V ≤ U ∧ (t : T) ∈ V ∧ AlgebraicGeometry.IsAffineOpen V ∧ P V)
    (H : ∀ (V : T.Opens) (hV : V ≤ U), AlgebraicGeometry.IsAffineOpen V → P V →
      T.homOfLE hV ≫ a = T.homOfLE hV ≫ b) : a = b := by
  choose V hVU htV hVaff hPV using hcov
  have hcover : TopologicalSpace.IsOpenCover (fun t : U => U.ι ⁻¹ᵁ V t) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, htV y⟩
  refine (U.toScheme.openCoverOfIsOpenCover (fun t : U => U.ι ⁻¹ᵁ V t) hcover).hom_ext _ _ fun t ↦ ?_
  change (U.ι ⁻¹ᵁ V t).ι ≫ a = (U.ι ⁻¹ᵁ V t).ι ≫ b
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ V t) = V t := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf, AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hVU t)
  have hι : (U.ι ⁻¹ᵁ V t).ι =
      (U.ι.isoImage (U.ι ⁻¹ᵁ V t)).hom ≫ (T.isoOfEq himg).hom ≫ T.homOfLE (hVU t) := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Category.assoc, AlgebraicGeometry.Scheme.homOfLE_ι,
      AlgebraicGeometry.Scheme.isoOfEq_hom_ι, AlgebraicGeometry.Scheme.Hom.isoImage_hom_ι]
  rw [hι]
  simp only [Category.assoc]
  rw [H (V t) (hVU t) (hVaff t) (hPV t)]

end HomExt

/-! ## Behaviour of `localRingHom` under change of chart and of trivialization -/

section LocalRingHomLeaves

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-! ### `projBundle.localRingHom` as an instance of the general `liftLocalRingHomAux` -/

set_option backward.isDefEq.respectTransparency.types false

private theorem dual_isQuasicoherent (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent := by
  have := AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
  exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _

/-- The `LiftData` of the projective bundle:
`Ψ_m := symGradedPullbackDesc f ψ m`, with `map_one` = `pullback_map_one_comp_symGradedPullbackDesc_zero`,
`map_mul` = `pullback_map_mul_comp_symGradedPullbackDesc`, `generates` from `symGradedPullbackDesc_one_epi`
(degree `1` generates, on the chart `⊤`).

This is exactly `relativeProj.liftDataOfEpi f V^∨ M ψ`, whose `IsQuasicoherent` instance argument is supplied
here by `isQuasicoherent_of_isLocallyFree` (a theorem, not an instance). The name is a reducible `abbrev`
because it packages the instance and appears in the statements of the lemmas below and in
`projBundle.lift`/`liftLocal`. -/
noncomputable abbrev liftData (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X) (M : T.Modules)
    [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [Epi ψ] :
    AlgebraicGeometry.Scheme.relativeProj.LiftData
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)) f M :=
  @AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi X T f (AlgebraicGeometry.Scheme.Modules.dual V)
    (dual_isQuasicoherent V) M _ ψ ‹_›

/-- `⊤ ≤ (ι ≫ f)⁻¹ᵁ W` for `ι = localRingHomIncl f U W` (same proof as `localRingHomBase_top_le`, restated with the
composite spelled out so that the type is syntactically the one `liftLocalRingHomAux` expects). -/
theorem incl_comp_top_le (f : T ⟶ X) (U : T.Opens) (W : X.Opens) :
    (⊤ : (U ⊓ f ⁻¹ᵁ W).toScheme.Opens) ≤ (localRingHomIncl f U W ≫ f) ⁻¹ᵁ W :=
  localRingHomBase_top_le f U W

/-- `projBundle.localRingHom` is the general `liftLocalRingHomAux` for `liftData`, `ι = localRingHomIncl`,
`e' = localRingHomTriv` (the two definitions are the same composite; `rfl` on each graded piece). -/
theorem localRingHom_eq_liftLocalRingHomAux (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [Epi ψ] (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    localRingHom V f M ψ U e W =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (liftData V f M ψ) (localRingHomIncl f U W)
        (localRingHomTriv f M U e W) W (incl_comp_top_le f U W) := by
  refine DirectSum.ringHom_ext fun m a => ?_
  exact (DirectSum.toSemiring_of (localRingHomComponent V f M ψ U e W) _ _ m a).trans
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of (liftData V f M ψ) (localRingHomIncl f U W)
      (localRingHomTriv f M U e W) W (incl_comp_top_le f U W) m a).symm

/-- **(4/6-C): `localRingHom` is compatible with restriction of the affine chart, up to a unit.**
For `W' ≤ W`, restricting the graded sections `A(W) → A(W')` (`sectionsRestrictRingHom`) and then applying the
local ring map on `U ⊓ f⁻¹W'` equals, on degree-`d` elements and up to the `d`-th power of a global unit `u` of
`Γ(U ⊓ f⁻¹W', O)`, applying the local ring map on `U ⊓ f⁻¹W` and restricting to `U ⊓ f⁻¹W' ⊆ U ⊓ f⁻¹W`.
(In truth `u = 1`; the weaker "up to a unit" form is what `fromOfGlobalSections_unit_scale` needs and what follows
directly from the general lemmas, see below.)

Source: Stacks 01O4 ("up to strict equivalence") / 01NQ (the local pieces of the morphism to `Proj` are compatible
with the gluing data of the relative Proj).

Proof. Write `ι := localRingHomIncl f U W : U ⊓ f⁻¹W → T`, `ι' := localRingHomIncl f U W'`,
`j := homOfLE : U ⊓ f⁻¹W' → U ⊓ f⁻¹W`, so `j ≫ ι = ι'` (`homOfLE_homOfLE`).
1. `projBundle.localRingHom V f M ψ U e W` is literally the general local ring map
   `relativeProj.liftLocalRingHomAux D ι (localRingHomTriv f M U e W) W _`
   for the `LiftData` `D` with `D.Ψ m := symGradedPullbackDesc f ψ m` (`map_one` = `pullback_map_one_comp_symGradedPullbackDesc_zero`,
   `map_mul` = `pullback_map_mul_comp_symGradedPullbackDesc`, `generates` from `symGradedPullbackDesc_one_epi`):
   the two definitions are the same composite `pullbackComp.inv ≫ ι^*(Ψ_m) ≫ pullbackMonoidalPow ≫ monoidalPowMap e' ≫ unitPowCollapse`
   evaluated on `⊤` after the adjunction unit (`DirectSum.ringHom_ext` + `rfl`).
2. For the general map one has
   `liftLocalRingHomAux_comp` (`j^♯ ∘ Aux(ι, e', W) = Aux(j ≫ ι, trivComp j ι M e', W)`),
   `liftLocalRingHomAux_restrict` (`Aux(ι, e', W) = Aux(ι, e', W') ∘ sectionsRestrict`),
   `liftLocalRingHomAux_congr` (transport along `ι = ι'` via `pullbackCongr`), and
   `liftLocalRingHomAux_unit_scale` (two trivializations of the same `ι^*M` change `Aux` by `u^d`,
   `u = unitEndSection (e₁'.inv ≫ e₂'.hom)`, a unit by `isUnit_unitEndSection_hom`).
3. Hence `res_j ∘ localRingHom(W) = Aux(j ≫ ι, trivComp …, W) = Aux(j ≫ ι, trivComp …, W') ∘ restrict
   = Aux(ι', E, W') ∘ restrict` with `E := (pullbackCongr (j ≫ ι = ι')).symm ≪≫ trivComp …`, while
   `localRingHom(W') = Aux(ι', localRingHomTriv f M U e W', W')`; the two trivializations `E`, `localRingHomTriv … W'`
   of `ι'^*M` differ by the unit `u`, which gives the claim. -/
theorem exists_unit_localRingHom_restrict_scale (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [Epi ψ] (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) {W W' : X.Opens}
    (h : W' ≤ W) :
    ∃ u : Γ((U ⊓ f ⁻¹ᵁ W').toScheme, ⊤)ˣ, ∀ (d : ℕ) (x : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRing W),
      x ∈ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsGrading W d →
      localRingHom V f M ψ U e W' ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRestrictRingHom h x) =
        (u : Γ((U ⊓ f ⁻¹ᵁ W').toScheme, ⊤)) ^ d *
          (T.homOfLE (inf_le_inf_left U (f.preimage_mono h))).appTop.hom.comp (localRingHom V f M ψ U e W) x := by
  have hι : T.homOfLE (inf_le_inf_left U (f.preimage_mono h)) ≫ localRingHomIncl f U W = localRingHomIncl f U W' := by
    unfold localRingHomIncl
    rw [← Category.assoc, AlgebraicGeometry.Scheme.homOfLE_homOfLE]
  have hW'₀ : (⊤ : (U ⊓ f ⁻¹ᵁ W').toScheme.Opens) ≤
      ((T.homOfLE (inf_le_inf_left U (f.preimage_mono h)) ≫ localRingHomIncl f U W) ≫ f) ⁻¹ᵁ W' := by
    intro y _
    show f.base ((T.homOfLE (inf_le_inf_left U (f.preimage_mono h)) ≫ localRingHomIncl f U W).base y) ∈ W'
    rw [hι]
    unfold localRingHomIncl
    rw [AlgebraicGeometry.Scheme.homOfLE_ι]
    exact y.2.2
  let E := ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hι).app M).symm ≪≫
    AlgebraicGeometry.Scheme.Modules.trivComp (T.homOfLE (inf_le_inf_left U (f.preimage_mono h)))
      (localRingHomIncl f U W) M (localRingHomTriv f M U e W)
  have eR : (T.homOfLE (inf_le_inf_left U (f.preimage_mono h))).appTop.hom.comp (localRingHom V f M ψ U e W) =
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (liftData V f M ψ) (localRingHomIncl f U W') E W'
        (incl_comp_top_le f U W')).comp
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRestrictRingHom h) := by
    rw [localRingHom_eq_liftLocalRingHomAux, AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_comp,
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_restrict _ _ _ h _ hW'₀]
    exact congrArg (fun k => RingHom.comp k _)
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_congr _ hι _ W' _ _).symm
  refine ⟨(AlgebraicGeometry.Scheme.Modules.isUnit_unitEndSection_hom (E.symm ≪≫ localRingHomTriv f M U e W')).unit,
    fun d x hx => ?_⟩
  have hx' : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRestrictRingHom h x ∈
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsGrading W' d :=
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRestrict h).map_mem hx
  rw [localRingHom_eq_liftLocalRingHomAux, eR, RingHom.comp_apply,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_unit_scale _ (localRingHomIncl f U W') E
      (localRingHomTriv f M U e W') W' _ d _ hx', IsUnit.unit_spec]
  rfl

/-- **(4/6-E): two trivializations change `localRingHom` by the powers of a unit.**
Given trivializations `e₁ : M|_{U₁} ≅ O`, `e₂ : M|_{U₂} ≅ O` and an open `V₃ ≤ (U₁ ⊓ f⁻¹W) ⊓ (U₂ ⊓ f⁻¹W)`, there is a
unit `u ∈ Γ(V₃, O)ˣ` with `res_{V₃}(localRingHom(U₂, e₂, W) x) = u^d · res_{V₃}(localRingHom(U₁, e₁, W) x)` for every
`x ∈ A(W)_d`. This is exactly the `hscale` hypothesis of `fromOfGlobalSections_unit_scale`.

Source: Stacks 01O4 ("up to strict equivalence": the pair `(L, ψ)` is determined up to a unit).

Proof.
1. On `V₃` both `e₁` and `e₂` restrict to trivializations `e₁', e₂' : M|_{V₃} ≅ O_{V₃}`
   (`localRingHomTriv` pulled back along `V₃ ↪ U_i ⊓ f⁻¹W`). The composite `e₂' ∘ e₁'⁻¹ : O_{V₃} ≅ O_{V₃}` is an
   automorphism of the unit module sheaf, hence multiplication by the global unit
   `u := (e₂' ∘ e₁'⁻¹).app ⊤ 1 ∈ Γ(V₃, O)ˣ` (`SheafOfModules.unitHomEquiv` / a `Modules` endomorphism of `O` is
   determined by the image of `1`; its inverse gives `u⁻¹`).
2. By definition (`localRingHomComponent_apply`), the degree-`d` component is
   `res (Φ_W.app ⊤ (…))` with `Φ_W = … ≫ pullbackMonoidalPow ι M d ≫ monoidalPowMap e'.hom d ≫ unitPowCollapse d`;
   the only factor depending on `e` is `monoidalPowMap e'.hom d`. Restricting to `V₃` (compatibility of all
   factors with the open immersion `V₃ ↪ U_i ⊓ f⁻¹W`, as in `exists_unit_localRingHom_restrict_scale`, via the general lemmas) both
   components become `Φ_common ≫ monoidalPowMap e_i'.hom d ≫ unitPowCollapse d` on `V₃`.
3. `monoidalPowMap e₂'.hom d = monoidalPowMap e₁'.hom d ≫ monoidalPowMap (e₂' ∘ e₁'⁻¹).hom d`
   (`monoidalPowMap` is functorial: `monoidalPowMap_comp`, by induction on `d` from `tensorHom_comp`), and
   `monoidalPowMap (mul u) d ≫ unitPowCollapse d = unitPowCollapse d ≫ mul (u^d)` (induction on `d`:
   `unitPowCollapse (d+1) = (unitPowCollapse d ▷ 𝟙_) ≫ λ_`, `(a ⊗ₘ b) ▷`/`λ_` naturality, `mul u ⊗ mul u = mul (u·u)`
   on `𝟙_ ⊗ 𝟙_` via `λ_`).
4. Hence on sections: `Φ²_d(a) = u^d · Φ¹_d(a)` in `Γ(V₃, O)`; extend from homogeneous elements to
   `x ∈ A(W)_d` (which are exactly `DirectSum.of d a`, `sectionsGrading`), using `DirectSum.toSemiring_of`.

Formalized from the general lemmas `liftLocalRingHomAux_comp` along `j_i : V₃ → U_i ⊓ f⁻¹W`,
`liftLocalRingHomAux_congr` to the common `ι = V₃.ι`, then `liftLocalRingHomAux_unit_scale` with
`u := unitEndSection (F₁.inv ≫ F₂.hom)`. -/
theorem exists_unit_localRingHom_scale (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (f : T ⟶ X)
    (M : T.Modules) [M.IsLineBundle]
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ M)
    [Epi ψ] (U₁ : T.Opens) (e₁ : M.restrict U₁.ι ≅ SheafOfModules.unit U₁.toScheme.ringCatSheaf)
    (U₂ : T.Opens) (e₂ : M.restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf) (W : X.Opens)
    (V₃ : T.Opens) (h₁ : V₃ ≤ U₁ ⊓ f ⁻¹ᵁ W) (h₂ : V₃ ≤ U₂ ⊓ f ⁻¹ᵁ W) :
    ∃ u : Γ(V₃.toScheme, ⊤)ˣ, ∀ (d : ℕ) (x : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsRing W),
      x ∈ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).sectionsGrading W d →
      (T.homOfLE h₂).appTop.hom.comp (localRingHom V f M ψ U₂ e₂ W) x =
        (u : Γ(V₃.toScheme, ⊤)) ^ d * (T.homOfLE h₁).appTop.hom.comp (localRingHom V f M ψ U₁ e₁ W) x := by
  have hι₁ : T.homOfLE h₁ ≫ localRingHomIncl f U₁ W = V₃.ι := by
    unfold localRingHomIncl
    rw [← Category.assoc, AlgebraicGeometry.Scheme.homOfLE_homOfLE, AlgebraicGeometry.Scheme.homOfLE_ι]
  have hι₂ : T.homOfLE h₂ ≫ localRingHomIncl f U₂ W = V₃.ι := by
    unfold localRingHomIncl
    rw [← Category.assoc, AlgebraicGeometry.Scheme.homOfLE_homOfLE, AlgebraicGeometry.Scheme.homOfLE_ι]
  have hW₀ : (⊤ : V₃.toScheme.Opens) ≤ (V₃.ι ≫ f) ⁻¹ᵁ W := fun y _ => (h₁ y.2).2
  let F₁ := ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hι₁).app M).symm ≪≫
    AlgebraicGeometry.Scheme.Modules.trivComp (T.homOfLE h₁) (localRingHomIncl f U₁ W) M (localRingHomTriv f M U₁ e₁ W)
  let F₂ := ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hι₂).app M).symm ≪≫
    AlgebraicGeometry.Scheme.Modules.trivComp (T.homOfLE h₂) (localRingHomIncl f U₂ W) M (localRingHomTriv f M U₂ e₂ W)
  have e₁' : (T.homOfLE h₁).appTop.hom.comp (localRingHom V f M ψ U₁ e₁ W) =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (liftData V f M ψ) V₃.ι F₁ W hW₀ := by
    rw [localRingHom_eq_liftLocalRingHomAux, AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_comp]
    exact (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_congr _ hι₁ _ W _ hW₀).symm
  have e₂' : (T.homOfLE h₂).appTop.hom.comp (localRingHom V f M ψ U₂ e₂ W) =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux (liftData V f M ψ) V₃.ι F₂ W hW₀ := by
    rw [localRingHom_eq_liftLocalRingHomAux, AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_comp]
    exact (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_congr _ hι₂ _ W _ hW₀).symm
  refine ⟨(AlgebraicGeometry.Scheme.Modules.isUnit_unitEndSection_hom (F₁.symm ≪≫ F₂)).unit, fun d x hx => ?_⟩
  rw [e₁', e₂', AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_unit_scale _ V₃.ι F₁ F₂ W hW₀ d x hx,
    IsUnit.unit_spec]
  rfl

end LocalRingHomLeaves

end AlgebraicGeometry.Scheme.projBundle

end
