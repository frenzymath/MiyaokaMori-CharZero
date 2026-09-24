import MiyaokaMori.Prelude

/-! # Auxiliary facts for the assembly of Chow's lemma

Small general lemmas used in the proof of Chow's lemma (Stacks 0200):

* `isIso_of_isOpenImmersion_of_isProper`: a proper open immersion with nonempty source into a
  (pre)irreducible scheme is an isomorphism (its range is a nonempty clopen set, hence everything).
* `preirreducibleSpace_opens`: an open subscheme of a preirreducible scheme is preirreducible.
* `isProper_of_isIso`: isomorphisms are proper.
* `isReduced_image`: the scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced
  (`Γ(im f, im f.ι⁻¹ U) → Γ(X, f⁻¹ U)` is injective for affine `U`, Mathlib `Hom.toImage_app_injective`).
* `isIntegral_image`: the scheme-theoretic image of a quasi-compact morphism from an integral scheme is
  integral (reduced by the above; irreducible because the range of `f.toImage` is dense and irreducible).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- An open subscheme of a preirreducible scheme is preirreducible (not registered as an instance). -/
theorem preirreducibleSpace_opens {Z : Scheme.{u}} [PreirreducibleSpace Z] (O : Z.Opens) :
    PreirreducibleSpace O :=
  O.ι.isOpenEmbedding.preirreducibleSpace

/-- Isomorphisms of schemes are proper. -/
theorem isProper_of_isIso {A B : Scheme.{u}} (φ : A ⟶ B) [IsIso φ] : IsProper φ := by
  have : IsClosedImmersion φ := inferInstance
  exact ⟨⟩

/-- A proper open immersion `φ : A ⟶ B` with `A ≠ ∅` into a preirreducible scheme `B` is an isomorphism:
its range is open, closed (proper ⇒ closed map) and nonempty, hence all of `B`, and a surjective open
immersion is an isomorphism (`IsOpenImmersion.isIso`). -/
theorem isIso_of_isOpenImmersion_of_isProper {A B : Scheme.{u}} (φ : A ⟶ B) [IsOpenImmersion φ]
    [IsProper φ] [PreirreducibleSpace B] [Nonempty A] : IsIso φ := by
  have hcl : IsClosed (Set.range φ.base) := φ.isClosedMap.isClosed_range
  have hop : IsOpen (Set.range φ.base) := φ.isOpenEmbedding.isOpen_range
  have hne : (Set.range φ.base).Nonempty := Set.range_nonempty _
  have hsurj : Function.Surjective φ.base := by
    rw [← Set.range_eq_univ]
    by_contra h
    obtain ⟨x, hx, hx'⟩ := nonempty_preirreducible_inter hop hcl.isOpen_compl hne
      (Set.nonempty_compl.mpr h)
    exact hx' hx
  have : Epi φ.base := (TopCat.epi_iff_surjective _).mpr hsurj
  exact IsOpenImmersion.isIso φ

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced. -/
theorem isReduced_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] [QuasiCompact f] :
    IsReduced f.image := by
  have hcov : ⨆ U : Y.affineOpens, f.imageι ⁻¹ᵁ U.1 = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  have : ∀ U : Y.affineOpens, IsReduced (f.imageι ⁻¹ᵁ U.1).toScheme := fun U => by
    have hU : IsAffineOpen (f.imageι ⁻¹ᵁ U.1) := U.2.preimage f.imageι
    have : IsAffine (f.imageι ⁻¹ᵁ U.1).toScheme := hU
    have hinj : Function.Injective
        ((f.imageι ⁻¹ᵁ U.1).topIso.hom ≫ f.toImage.app (f.imageι ⁻¹ᵁ U.1)).hom :=
      (f.toImage_app_injective U).comp
        ((f.imageι ⁻¹ᵁ U.1).topIso.commRingCatIsoToRingEquiv.injective)
    have : _root_.IsReduced Γ((f.imageι ⁻¹ᵁ U.1).toScheme, ⊤) := isReduced_of_injective _ hinj
    exact isReduced_of_isAffine_isReduced _
  haveI : ∀ i, IsReduced ((f.image.openCoverOfIsOpenCover _ hcov).X i) := fun U => this U
  exact IsReduced.of_openCover f.image (f.image.openCoverOfIsOpenCover _ hcov)

/-- The scheme-theoretic image of a quasi-compact morphism from an integral scheme is integral:
reduced (`isReduced_image`), and irreducible because the range of `f.toImage` is dense (Mathlib
`IsDominant f.toImage`) and irreducible (image of an irreducible space). -/
theorem isIntegral_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [QuasiCompact f] :
    IsIntegral f.image := by
  have : IsReduced f.image := isReduced_image f
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def, Set.top_eq_univ]
    have h1 : IsIrreducible (Set.range f.toImage.base) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.base.hom.continuous.continuousOn
    have h2 : closure (Set.range f.toImage.base) = Set.univ := f.toImage.denseRange.closure_range
    rw [← h2]
    exact h1.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

end AlgebraicGeometry

end
