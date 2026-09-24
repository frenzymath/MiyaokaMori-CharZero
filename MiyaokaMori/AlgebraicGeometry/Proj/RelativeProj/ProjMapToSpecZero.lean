import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Proj maps preserve their structure morphisms

A graded ring map `f : 𝒜 →+*ᵍ ℬ` satisfying the irrelevant-ideal condition `ℬ₊ ≤ 𝒜₊.map f`
induces an everywhere-defined Proj map `Proj.map f hf : Proj ℬ ⟶ Proj 𝒜`. Its structure
morphism to the spectrum of the degree-zero ring is natural:

  `Proj.map f hf ≫ Proj.toSpecZero 𝒜 = Proj.toSpecZero ℬ ≫ Spec.map (ofHom f.gradedZeroRingHom)`

The proof checks the two composites on Mathlib's affine open cover `Proj.mapAffineOpenCover f hf`
of `Proj ℬ`: on the chart `D₊(f s)`, both send a degree-zero element `a` to `a / 1`
(`awayMap_fromZero`).

Used by: `Scheme.GradedAffineAlgebra.projToOpen_naturality` (`RelativeProj.lean`), the
`P^1`/`P^n` structure-morphism lemmas, `Proj.map_congrGradingHom_toSpecZero`, Stacks 01WC/0804.

Sources: Stacks Project, `constructions.tex`, `lemma-morphism-proj` (the maps on homogeneous
localizations) and `lemma-proj-inclusion` (the same local Proj schemes over their affine base opens);
the relative Proj `Y_k^GG = Proj_C 𝒮` of §2 of the paper.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open scoped HomogeneousIdeal

namespace AlgebraicGeometry.Proj

universe u

section GradedRingMap

variable {R S σ τ : Type u} [CommRing R] [CommRing S]
  [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ S] [AddSubgroupClass τ S]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)

/-- On degree-zero coefficients, the localization map is the map of fractions `a/1`. -/
private theorem awayMap_fromZero (s : R) (a : 𝒜 0) :
    Away.map f s (fromZeroRingHom 𝒜 _ a) =
      fromZeroRingHom ℬ _ (f.gradedZeroRingHom a) := by
  apply HomogeneousLocalization.val_injective
  change HomogeneousLocalization.val
      (HomogeneousLocalization.map f _
        (HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩)) =
    HomogeneousLocalization.val
      (HomogeneousLocalization.mk ⟨0, f.gradedAddHom 0 a, 1, one_mem _⟩)
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The actual Proj map commutes with the structure maps to the degree-zero spectra. -/
theorem proj_map_toSpecZero (hf : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f,
    AlgebraicGeometry.Proj.mapAffineOpenCover_f]
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 _ s.2.2,
    Category.assoc, Proj.awayι_toSpecZero, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact awayMap_fromZero f s.2 a

end GradedRingMap
end AlgebraicGeometry.Proj
