import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjMapToSpecZero

/-! # Transport of `Proj` along two encodings of the same grading

**Transport of `Proj` between two `SetLike` encodings of the same grading.** Let `𝒜 : ℕ → σ` and
`𝒜' : ℕ → τ` be two gradings of the same ring `A` with the same members (`x ∈ 𝒜 i ↔ x ∈ 𝒜' i`),
both `GradedRing`s. Typical case: `𝒜` `AddSubgroup`-valued (as in `Scheme.GradedAffineAlgebra.grading`)
and `𝒜'` `Submodule R`-valued (as required by the base-change statements of Stacks 01N2,
`Proj.isPullback_of_isBaseChange`, which need `GradedAlgebra`). Then

* `congrGradingHom 𝒜 𝒜' h : 𝒜 →+*ᵍ 𝒜'` is the identity of `A` as a graded ring hom,
  with the irrelevant-ideal condition `irrelevant_le_map_congrGradingHom` needed by `Proj.map`;
* `Proj.map (congrGradingHom 𝒜 𝒜' h) : Proj 𝒜' ⟶ Proj 𝒜` and `Proj.map (congrGradingHom 𝒜' 𝒜 _)`
  are inverse (`congrGradingIso : Proj 𝒜' ≅ Proj 𝒜`; `Proj.map_comp`, `Proj.map_id`);
* `congrGradingHom_map_toSpecZero`: compatibility with the structure maps to the degree-zero spectra
  (`AlgebraicGeometry.Proj.proj_map_toSpecZero`, natural in the graded ring hom).

Only membership is used: no relation between the two `decompose` data is needed.

Source: Mathlib `AlgebraicGeometry/ProjectiveSpectrum/Functor.lean` (`Proj.map`, `map_comp`,
`map_id`); `ProjMapToSpecZero.lean` (`proj_map_toSpecZero`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory
open scoped HomogeneousIdeal

noncomputable section

namespace AlgebraicGeometry.Proj

/-- `Proj.map` depends only on the graded ring hom (transport of the proof argument). -/
theorem map_congr_hom {A B : Type u} [CommRing A] [CommRing B] {σ ψ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] [SetLike ψ B] [AddSubgroupClass ψ B] {𝒜 : ℕ → σ} {ℬ : ℕ → ψ}
    [GradedRing 𝒜] [GradedRing ℬ] {f g : 𝒜 →+*ᵍ ℬ} (e : f = g) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hg : ℬ₊ ≤ 𝒜₊.map g) : Proj.map f hf = Proj.map g hg := by
  subst e; rfl

variable {A : Type u} [CommRing A] {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ℕ → σ) (𝒜' : ℕ → τ) [GradedRing 𝒜] [GradedRing 𝒜']
  (h : ∀ (i : ℕ) (x : A), x ∈ 𝒜 i ↔ x ∈ 𝒜' i)

/-- The identity of `A` as a graded ring hom between two encodings of the same grading. -/
def congrGradingHom : 𝒜 →+*ᵍ 𝒜' where
  toRingHom := RingHom.id A
  map_mem hx := (h _ _).1 hx

@[simp] theorem congrGradingHom_apply (x : A) : congrGradingHom 𝒜 𝒜' h x = x := rfl

/-- Symmetric membership hypothesis. -/
theorem congr_symm (h : ∀ (i : ℕ) (x : A), x ∈ 𝒜 i ↔ x ∈ 𝒜' i) :
    ∀ (i : ℕ) (x : A), x ∈ 𝒜' i ↔ x ∈ 𝒜 i := fun i x => (h i x).symm

/-- The irrelevant-ideal condition of `Proj.map` for `congrGradingHom`. -/
theorem irrelevant_le_map_congrGradingHom :
    𝒜'₊ ≤ 𝒜₊.map (congrGradingHom 𝒜 𝒜' h) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  exact Ideal.mem_map_of_mem (congrGradingHom 𝒜 𝒜' h)
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi ((h i x).2 hx))

theorem congrGradingHom_comp_congrGradingHom :
    (congrGradingHom 𝒜' 𝒜 (congr_symm 𝒜 𝒜' h)).comp (congrGradingHom 𝒜 𝒜' h) =
      GradedRingHom.id 𝒜 :=
  GradedRingHom.ext fun _ => rfl

theorem map_congrGradingHom_comp_map_congrGradingHom :
    Proj.map (congrGradingHom 𝒜 𝒜' h) (irrelevant_le_map_congrGradingHom 𝒜 𝒜' h) ≫
      Proj.map (congrGradingHom 𝒜' 𝒜 (congr_symm 𝒜 𝒜' h))
        (irrelevant_le_map_congrGradingHom 𝒜' 𝒜 (congr_symm 𝒜 𝒜' h)) = 𝟙 (Proj 𝒜') := by
  rw [← Proj.map_comp]
  exact (map_congr_hom (congrGradingHom_comp_congrGradingHom 𝒜' 𝒜 (congr_symm 𝒜 𝒜' h)) _
    (by simp)).trans Proj.map_id

/-- The canonical isomorphism `Proj 𝒜' ≅ Proj 𝒜` between the two encodings. -/
def congrGradingIso : Proj 𝒜' ≅ Proj 𝒜 where
  hom := Proj.map (congrGradingHom 𝒜 𝒜' h) (irrelevant_le_map_congrGradingHom 𝒜 𝒜' h)
  inv := Proj.map (congrGradingHom 𝒜' 𝒜 (congr_symm 𝒜 𝒜' h))
    (irrelevant_le_map_congrGradingHom 𝒜' 𝒜 (congr_symm 𝒜 𝒜' h))
  hom_inv_id := map_congrGradingHom_comp_map_congrGradingHom 𝒜 𝒜' h
  inv_hom_id := map_congrGradingHom_comp_map_congrGradingHom 𝒜' 𝒜 (congr_symm 𝒜 𝒜' h)

/-- `Proj.map` of the identity graded hom is an isomorphism (not an instance; supply locally with
`haveI := isIso_map_congrGradingHom …` where needed). -/
theorem isIso_map_congrGradingHom :
    IsIso (Proj.map (congrGradingHom 𝒜 𝒜' h) (irrelevant_le_map_congrGradingHom 𝒜 𝒜' h)) :=
  (congrGradingIso 𝒜 𝒜' h).isIso_hom

/-- Compatibility with the structure maps to the degree-zero spectra. -/
theorem map_congrGradingHom_toSpecZero :
    Proj.map (congrGradingHom 𝒜 𝒜' h) (irrelevant_le_map_congrGradingHom 𝒜 𝒜' h) ≫
        Proj.toSpecZero 𝒜 =
      Proj.toSpecZero 𝒜' ≫
        Spec.map (CommRingCat.ofHom (congrGradingHom 𝒜 𝒜' h).gradedZeroRingHom) :=
  AlgebraicGeometry.Proj.proj_map_toSpecZero (congrGradingHom 𝒜 𝒜' h) _

end AlgebraicGeometry.Proj

end
