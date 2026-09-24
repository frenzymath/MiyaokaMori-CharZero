import MiyaokaMori.Prelude

/-! # `Proj.fromOfGlobalSections` is compatible with `Proj.map`

Compatibility of `Proj.fromOfGlobalSections` with `Proj.map`: for a graded ring homomorphism
`ρ : 𝒜 →+*ᵍ ℬ` satisfying the irrelevant-ideal condition of `Proj.map` (`ℬ₊ ≤ ρ(𝒜₊)`) and
`φ : B →+* Γ(Y, ⊤)` with `φ(ℬ₊) = ⊤`,

  `fromOfGlobalSections ℬ φ ≫ Proj.map ρ = fromOfGlobalSections 𝒜 (φ ∘ ρ)`.

Source: Stacks 01O4 (morphisms to Proj are given by graded ring maps to the ring of global sections,
functorially in the graded ring). The proof is a direct comparison of the definition of Mathlib's
`Proj.fromOfGlobalSections` (gluing `toBasicOpenOfGlobalSections` along the open cover `D(φ(ρ t))`)
with `Proj.awayι_comp_map`. Used in the change-of-affine-open step `W₁ ↝ W₃` of
`relativeProj.liftLocal_compat` (`RelativeProjLift.lean`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open CategoryTheory Opposite TopologicalSpace HomogeneousLocalization HomogeneousIdeal Graded
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {A B : Type u} [CommRing A] [CommRing B] {σ τ : Type u}
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The irrelevant-ideal condition passes along a composite: `ℬ₊ ≤ ρ(𝒜₊)` and `φ(ℬ₊) = ⊤` imply
`(φ ∘ ρ)(𝒜₊) = ⊤`. -/
theorem irrelevant_map_comp_eq_top_of_map_eq_top {R : Type v} [CommRing R]
    (ρ : 𝒜 →+*ᵍ ℬ) (hρ : irrelevant ℬ ≤ (irrelevant 𝒜).map ρ)
    (φ : B →+* R) (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    (irrelevant 𝒜).toIdeal.map (φ.comp ρ.toRingHom) = ⊤ := by
  rw [← Ideal.map_map, _root_.eq_top_iff, ← hφ]
  exact Ideal.map_mono (hρ : (irrelevant ℬ).toIdeal ≤ ((irrelevant 𝒜).map ρ).toIdeal)

variable {Y : Scheme.{u}}

/-- `D(φ t) ↪ Y ≫ fromOfGlobalSections` is the chart `toBasicOpenOfGlobalSections ≫ D₊(t) ↪ Proj`
(a rewriting of Mathlib's `fromOfGlobalSections_resLE`). -/
private theorem basicOpen_ι_fromOfGlobalSections_pfcm (f : A →+* Γ(Y, ⊤))
    (hf : (irrelevant 𝒜).toIdeal.map f = ⊤) {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    (Y.basicOpen (f t)).ι ≫ fromOfGlobalSections 𝒜 f hf =
      toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (basicOpen 𝒜 t).ι := by
  rw [← fromOfGlobalSections_resLE 𝒜 f hf hd ht]
  exact (Scheme.Hom.resLE_comp_ι (fromOfGlobalSections 𝒜 f hf)
    (fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hd ht).ge).symm

/-- The ring-map identity on homogeneous localizations:
`(loc φ ∘ alg_ℬ) ∘ Away.map ρ t = loc (φ ∘ ρ) ∘ alg_𝒜`. -/
private theorem localization_map_comp_awayMap_pfcm (ρ : 𝒜 →+*ᵍ ℬ) {R : Type v} [CommRing R]
    (φ : B →+* R) (t : A)
    (h₁ : Submonoid.powers (ρ t) ≤ (Submonoid.powers (φ (ρ t))).comap φ)
    (h₂ : Submonoid.powers t ≤ (Submonoid.powers (φ (ρ t))).comap (φ.comp ρ.toRingHom)) :
    ((IsLocalization.map (Localization.Away (φ (ρ t))) φ h₁ :
        Localization.Away (ρ t) →+* Localization.Away (φ (ρ t))).comp
      (algebraMap (Away ℬ (ρ t)) (Localization.Away (ρ t)))).comp
        (HomogeneousLocalization.Away.map ρ t) =
    (IsLocalization.map (Localization.Away (φ (ρ t))) (φ.comp ρ.toRingHom) h₂ :
        Localization.Away t →+* Localization.Away (φ (ρ t))).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t)) := by
  ext x
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [RingHom.comp_apply, HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Compatibility of `fromOfGlobalSections` with `Proj.map`**:
`fromOfGlobalSections ℬ φ ≫ Proj.map ρ = fromOfGlobalSections 𝒜 (φ ∘ ρ)`.

Proof: both sides are morphisms `Y → Proj 𝒜`; compare them (`Cover.hom_ext`) on the open cover
`{D(φ(ρ t)) : t ∈ 𝒜 d, d > 0}` of `Y` (`openCoverOfMapIrrelevantEqTop 𝒜 (φ ∘ ρ)`). On each piece
the left side becomes, by `fromOfGlobalSections_resLE` (for `ℬ` and the element `ρ t`),
`toBasicOpenOfGlobalSections ℬ φ ≫ D₊(ρ t).ι ≫ Proj.map ρ`, and then by `Proj.ι_comp_map` and
`awayι_comp_map`, `toBasicOpenOfGlobalSections ℬ φ ≫ (basicOpenIsoSpec ℬ).hom ≫
Spec.map (Away.map ρ t) ≫ (basicOpenIsoSpec 𝒜).inv ≫ D₊(t).ι`; unfolding
`toBasicOpenOfGlobalSections`, the two sides differ only in the last `Spec.map`, whose ring-map
identity is `localization_map_comp_awayMap_pfcm`. -/
theorem fromOfGlobalSections_comp_map (ρ : 𝒜 →+*ᵍ ℬ) (hρ : irrelevant ℬ ≤ (irrelevant 𝒜).map ρ)
    (φ : B →+* Γ(Y, ⊤)) (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    fromOfGlobalSections ℬ φ hφ ≫ Proj.map ρ hρ =
      fromOfGlobalSections 𝒜 (φ.comp ρ.toRingHom)
        (irrelevant_map_comp_eq_top_of_map_eq_top 𝒜 ℬ ρ hρ φ hφ) := by
  set ψ := φ.comp ρ.toRingHom with hψ
  set hψ' := irrelevant_map_comp_eq_top_of_map_eq_top 𝒜 ℬ ρ hρ φ hφ
  refine (openCoverOfMapIrrelevantEqTop 𝒜 ψ hψ').hom_ext _ _ fun ri => ?_
  rcases ri with ⟨d, t, hd, ht⟩
  change (Y.basicOpen (ψ t)).ι ≫ (fromOfGlobalSections ℬ φ hφ ≫ Proj.map ρ hρ) =
    (Y.basicOpen (ψ t)).ι ≫ fromOfGlobalSections 𝒜 ψ hψ'
  have hρt : ρ t ∈ ℬ d := map_mem ρ ht
  -- left side: go through the chart of ℬ first
  have hL : (Y.basicOpen (ψ t)).ι ≫ (fromOfGlobalSections ℬ φ hφ ≫ Proj.map ρ hρ) =
      toBasicOpenOfGlobalSections ℬ φ rfl hd hρt ≫ (basicOpen ℬ (ρ t)).ι ≫ Proj.map ρ hρ := by
    rw [← Category.assoc]
    exact congrArg (fun k => k ≫ Proj.map ρ hρ)
      (basicOpen_ι_fromOfGlobalSections_pfcm ℬ φ hφ hd hρt) |>.trans (Category.assoc _ _ _)
  rw [hL, basicOpen_ι_fromOfGlobalSections_pfcm 𝒜 ψ hψ' hd ht]
  -- `D₊(ρ t).ι ≫ Proj.map ρ = (basicOpenIsoSpec ℬ).hom ≫ Spec.map (Away.map ρ t) ≫ awayι 𝒜 t`
  have hmap : (basicOpen ℬ (ρ t)).ι ≫ Proj.map ρ hρ =
      (basicOpenIsoSpec ℬ (ρ t) hρt hd).hom ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ρ t)) ≫ awayι 𝒜 t ht hd := by
    rw [← awayι_comp_map ρ hρ hd t ht, ← basicOpenIsoSpec_inv_ι, ← Category.assoc,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hmap, ← basicOpenIsoSpec_inv_ι]
  simp only [← Category.assoc]
  congr 1
  -- unfold the two `toBasicOpenOfGlobalSections`
  simp only [toBasicOpenOfGlobalSections, Category.assoc, Iso.inv_hom_id_assoc]
  congr 3
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact localization_map_comp_awayMap_pfcm 𝒜 ℬ ρ φ t _ _

end AlgebraicGeometry.Proj

end
