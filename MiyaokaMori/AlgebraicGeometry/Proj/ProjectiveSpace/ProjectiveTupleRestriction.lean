import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue

/-!
# Restricting the canonical projectivization of a tuple

The projectivization of the polynomial tuple of Theorem 4.2 of the paper must agree on smaller
frame domains with the construction using the restricted coordinate sections.
These ordinary helpers prove that compatibility for Mathlib's actual
`Proj.fromOfGlobalSections`, first along an arbitrary scheme morphism and then
along the inclusion of one open subset in another.

The proof compares the actual localization ring maps on each homogeneous
chart, including the source-to-affine leg, and then uses an actual open cover.
This follows the degree-zero localization construction and restriction
uniqueness in Stacks Project, Lemma 27.14.1 (Tag 01NK). It does not assume
agreement of projective maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj.ProjectiveTupleRestriction

universe u v w

section Localization

variable {A : Type u} {R : Type v} {B : Type w}
    [CommRing A] [CommRing R] [CommRing B]

private theorem awayMap_comp_algebraMap (f : A →+* R) (t : A) :
    (Localization.awayMap f t).comp (algebraMap A (Localization.Away t)) =
      (algebraMap R (Localization.Away (f t))).comp f := by
  exact IsLocalization.map_comp _

private theorem awayMap_comp (f : A →+* R) (g : R →+* B) (t : A) :
    (Localization.awayMap g (f t)).comp (Localization.awayMap f t) =
      Localization.awayMap (g.comp f) t := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
  ext x
  simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_eq]

end Localization

section SourceLocalization

variable {S T : Scheme.{u}}

/-- The source-to-affine subexpression in Mathlib's local Proj construction. -/
private def affineLocalizationLeg (T : Scheme.{u}) (x : Γ(T, ⊤)) :
    (T.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  (T.isoOfEq (T.toSpecΓ_preimage_basicOpen x)).inv ≫
    T.toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫ (basicOpenIsoSpecAway x).hom

private theorem affineLocalizationLeg_comp (T : Scheme.{u}) (x : Γ(T, ⊤)) :
    affineLocalizationLeg T x ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away x))) =
        (T.basicOpen x).ι ≫ T.toSpecΓ := by
  simp only [affineLocalizationLeg, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [morphismRestrict_ι T.toSpecΓ (PrimeSpectrum.basicOpen x)]
  exact Scheme.isoOfEq_inv_ι_assoc T (T.toSpecΓ_preimage_basicOpen x) T.toSpecΓ

private theorem affineLocalizationLeg_naturality (h : S ⟶ T) (x : Γ(T, ⊤)) :
    h.resLE (T.basicOpen x) (S.basicOpen (h.appTop x))
        (h.preimage_basicOpen_top x).ge ≫ affineLocalizationLeg T x =
      affineLocalizationLeg S (h.appTop x) ≫
        Spec.map (CommRingCat.ofHom (Localization.awayMap h.appTop.hom x)) := by
  have hcomm :
      CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away x)) ≫
          CommRingCat.ofHom (Localization.awayMap h.appTop.hom x) =
        h.appTop ≫ CommRingCat.ofHom
          (algebraMap Γ(S, ⊤) (Localization.Away (h.appTop x))) := by
    exact congrArg (fun f : Γ(T, ⊤) →+* Localization.Away (h.appTop x) ↦
      CommRingCat.ofHom f) (awayMap_comp_algebraMap h.appTop.hom x)
  apply (cancel_mono
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away x))))).mp
  calc
    _ = (S.basicOpen (h.appTop x)).ι ≫ h ≫ T.toSpecΓ := by
      simp only [Category.assoc, affineLocalizationLeg_comp, Scheme.Hom.resLE_comp_ι_assoc]
    _ = (S.basicOpen (h.appTop x)).ι ≫ S.toSpecΓ ≫ Spec.map h.appTop := by
      rw [Scheme.toSpecΓ_naturality]
    _ = (affineLocalizationLeg S (h.appTop x) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, ⊤) (Localization.Away (h.appTop x))))) ≫
            Spec.map h.appTop := by
      rw [affineLocalizationLeg_comp, Category.assoc]
    _ = _ := by simp only [Category.assoc, ← Spec.map_comp, hcomm]

end SourceLocalization

section GradedEvaluation

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The irrelevant-ideal condition is preserved by composition with a ring
homomorphism, so it remains available after pulling back the coordinates. -/
theorem irrelevant_map_eq_top_comp {R : Type w} {B : Type*} [CommRing R] [CommRing B]
    (f : A →+* R) (g : R →+* B)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.comp f) = ⊤ := by
  rw [← Ideal.map_map, hf, Ideal.map_top]

variable {S T : Scheme.{u}}

private theorem toBasicOpenOfGlobalSections_eq (f : A →+* Γ(T, ⊤))
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
      affineLocalizationLeg T (f t) ≫
        Spec.map (CommRingCat.ofHom ((Localization.awayMap f t).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) ≫
        (Proj.basicOpenIsoSpec 𝒜 t ht hd).inv := by
  simp only [Proj.toBasicOpenOfGlobalSections, affineLocalizationLeg,
    Localization.awayMap, IsLocalization.Away.map, Category.assoc]

/-- The actual local Proj map commutes with pullback of its global sections.
Both sides are morphisms of schemes on the same source basic open. -/
theorem toBasicOpenOfGlobalSections_naturality (h : S ⟶ T) (f : A →+* Γ(T, ⊤))
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    h.resLE (T.basicOpen (f t)) (S.basicOpen ((h.appTop.hom.comp f) t))
        (h.preimage_basicOpen_top (f t)).ge ≫
          Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
      Proj.toBasicOpenOfGlobalSections 𝒜 (h.appTop.hom.comp f) rfl hd ht := by
  have hleg :
      h.resLE (T.basicOpen (f t)) (S.basicOpen ((h.appTop.hom.comp f) t))
          (h.preimage_basicOpen_top (f t)).ge ≫ affineLocalizationLeg T (f t) =
        affineLocalizationLeg S ((h.appTop.hom.comp f) t) ≫
          Spec.map (CommRingCat.ofHom (Localization.awayMap h.appTop.hom (f t))) :=
    affineLocalizationLeg_naturality h (f t)
  have hspec :
      Spec.map (CommRingCat.ofHom (Localization.awayMap h.appTop.hom (f t))) ≫
          Spec.map (CommRingCat.ofHom ((Localization.awayMap f t).comp
            (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) =
        Spec.map (CommRingCat.ofHom ((Localization.awayMap (h.appTop.hom.comp f) t).comp
          (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, awayMap_comp]
  rw [toBasicOpenOfGlobalSections_eq, toBasicOpenOfGlobalSections_eq,
    ← Category.assoc _ (affineLocalizationLeg T (f t)), hleg]
  simpa only [Category.assoc] using congrArg
    (fun m ↦ affineLocalizationLeg S ((h.appTop.hom.comp f) t) ≫ m ≫
      (Proj.basicOpenIsoSpec 𝒜 t ht hd).inv) hspec

private theorem basicOpen_ι_fromOfGlobalSections (f : A →+* Γ(T, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    (T.basicOpen (f t)).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (Proj.basicOpen 𝒜 t).ι := by
  rw [← Proj.fromOfGlobalSections_resLE 𝒜 f hf hd ht]
  exact (Scheme.Hom.resLE_comp_ι (Proj.fromOfGlobalSections 𝒜 f hf)
    (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hd ht).ge).symm

/-- Composing the canonical Proj morphism with an actual scheme morphism is
the same as first pulling back its coordinate sections and then constructing
the canonical Proj morphism. The new ideal condition is derived from `hf`. -/
theorem fromOfGlobalSections_naturality (h : S ⟶ T) (f : A →+* Γ(T, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    h ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.fromOfGlobalSections 𝒜 (h.appTop.hom.comp f)
        (irrelevant_map_eq_top_comp 𝒜 f h.appTop.hom hf) := by
  let g := h.appTop.hom.comp f
  let hg := irrelevant_map_eq_top_comp 𝒜 f h.appTop.hom hf
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 g hg).hom_ext _ _ fun ri ↦ ?_
  rcases ri with ⟨d, t, hd, ht⟩
  change (S.basicOpen (g t)).ι ≫ (h ≫ Proj.fromOfGlobalSections 𝒜 f hf) =
    (S.basicOpen (g t)).ι ≫ Proj.fromOfGlobalSections 𝒜 g hg
  let e := (h.preimage_basicOpen_top (f t)).ge
  calc
    _ = h.resLE (T.basicOpen (f t)) (S.basicOpen (g t)) e ≫
        (T.basicOpen (f t)).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf := by
      exact (Scheme.Hom.resLE_comp_ι_assoc h e (Proj.fromOfGlobalSections 𝒜 f hf)).symm
    _ = h.resLE (T.basicOpen (f t)) (S.basicOpen (g t)) e ≫
        Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫
          (Proj.basicOpen 𝒜 t).ι := by
      rw [basicOpen_ι_fromOfGlobalSections 𝒜 f hf hd ht]
    _ = Proj.toBasicOpenOfGlobalSections 𝒜 g rfl hd ht ≫
        (Proj.basicOpen 𝒜 t).ι := by
      rw [← Category.assoc, toBasicOpenOfGlobalSections_naturality 𝒜 h f hd ht]
    _ = _ := (basicOpen_ι_fromOfGlobalSections 𝒜 g hg hd ht).symm

/-- Restriction from an open `V` to an open `U ≤ V` commutes with the canonical
projectivization of the tuple; restricted nonvanishing follows from the original. -/
theorem fromOfGlobalSections_homOfLE (T : Scheme.{u}) (U V : T.Opens) (hUV : U ≤ V)
    (f : A →+* Γ(V.toScheme, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    T.homOfLE hUV ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.fromOfGlobalSections 𝒜 ((T.homOfLE hUV).appTop.hom.comp f)
        (irrelevant_map_eq_top_comp 𝒜 f (T.homOfLE hUV).appTop.hom hf) := by
  exact fromOfGlobalSections_naturality 𝒜 (T.homOfLE hUV) f hf

end GradedEvaluation

end AlgebraicGeometry.Proj.ProjectiveTupleRestriction
