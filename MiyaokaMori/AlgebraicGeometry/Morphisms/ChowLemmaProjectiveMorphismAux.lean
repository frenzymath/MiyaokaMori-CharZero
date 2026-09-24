import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveBaseChange

/-! # Auxiliary facts for Chow's lemma over a Noetherian affine base

Small general lemmas used for Chow's lemma over a Noetherian affine base
(`ChowLemmaNoetherianAffineBase.lean`, Stacks 0200):

* `isProjectiveMorphism_pullback_fst`: the first projection of `pullback g f` is projective when `f` is
  (the base change `IsProjectiveMorphism.baseChange` read through `pullbackSymmetry`).
* `isProjectiveMorphism_of_isClosedImmersion_comp`: a closed immersion followed by a projective morphism is
  projective (Stacks 01W7-type statement; immediate from the definition of `IsProjectiveMorphism`).
* `isClosedImmersion_of_isImmersion_of_isProper`: a proper immersion is a closed immersion (Stacks 01W6).
* `isImmersion_of_preimage_cover`: a morphism `h : X ⟶ Y` is an immersion as soon as there are opens `O i`
  of `Y` whose preimages cover `X` and such that each `(h ⁻¹ᵁ O i).ι ≫ h` is an immersion (immersions are
  local on the target; the range of `h` lies in `⨆ O i`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The first projection of a fibre product along a projective morphism is projective
(`IsProjectiveMorphism.baseChange` composed with the symmetry of the pullback). -/
theorem isProjectiveMorphism_pullback_fst {X Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (f : X ⟶ Y)
    [IsProjectiveMorphism f] : IsProjectiveMorphism (pullback.fst g f) := by
  have hsnd : IsProjectiveMorphism (pullback.snd f g) := IsProjectiveMorphism.baseChange f g
  obtain ⟨S, i, hgen, hft, hi, hfac⟩ := hsnd.exists_closed_immersion
  refine ⟨S, (pullbackSymmetry g f).hom ≫ i, hgen, hft, inferInstance, ?_⟩
  rw [Category.assoc, hfac, pullbackSymmetry_hom_comp_snd]

/-- A closed immersion into the source of a projective morphism, composed with it, is projective: compose
the closed immersion with the closed immersion into the relative Proj given by the definition. -/
theorem isProjectiveMorphism_of_isClosedImmersion_comp {X Y Z : Scheme.{u}} (c : X ⟶ Y) (f : Y ⟶ Z)
    [IsClosedImmersion c] [IsProjectiveMorphism f] : IsProjectiveMorphism (c ≫ f) := by
  obtain ⟨S, i, hgen, hft, hi, hfac⟩ := IsProjectiveMorphism.exists_closed_immersion (f := f)
  refine ⟨S, c ≫ i, hgen, hft, inferInstance, ?_⟩
  rw [Category.assoc, hfac]

/-- A proper immersion is a closed immersion (Stacks 01W6): its range is closed since a proper morphism is
a closed map, and an immersion with closed range is a closed immersion. -/
theorem isClosedImmersion_of_isImmersion_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    [IsProper f] : IsClosedImmersion f :=
  IsClosedImmersion.of_isPreimmersion f (by simpa [← Set.image_univ] using f.isClosedMap _ isClosed_univ)

/-- Immersions are local on the target: if opens `O i ⊆ Y` have preimages covering `X` and each restriction
`(h ⁻¹ᵁ O i).ι ≫ h : h ⁻¹ᵁ O i ⟶ Y` is an immersion, then `h` is an immersion. Proof: `h` factors through
the open `Q := ⨆ O i` as `h' ≫ Q.ι`; `h'` is an immersion because immersions are Zariski-local on the target
(`IsLocalAtTarget.of_iSup_eq_top` over the cover `Q.ι ⁻¹ᵁ O i` of `Q`) and `h' ∣_ (Q.ι ⁻¹ᵁ O i)` composed
with the open immersion `(Q.ι ⁻¹ᵁ O i).ι ≫ Q.ι` is `(h ⁻¹ᵁ O i).ι ≫ h`; then `h = h' ≫ Q.ι` is an immersion. -/
theorem isImmersion_of_preimage_cover {X Y : Scheme.{u}} (h : X ⟶ Y) {ι : Type*} (O : ι → Y.Opens)
    (hcov : h ⁻¹ᵁ (⨆ i, O i) = ⊤) (hloc : ∀ i, IsImmersion ((h ⁻¹ᵁ O i).ι ≫ h)) : IsImmersion h := by
  set Q : Y.Opens := ⨆ i, O i with hQ
  have hrange : Set.range h.base ⊆ Set.range Q.ι.base := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ h ⁻¹ᵁ Q := by rw [hcov]; trivial
    exact ⟨⟨h.base x, hx⟩, rfl⟩
  set h' : X ⟶ Q := IsOpenImmersion.lift Q.ι h hrange with hh'
  have hfac : h' ≫ Q.ι = h := IsOpenImmersion.lift_fac Q.ι h hrange
  have hh'imm : IsImmersion h' := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsImmersion)
      (fun i => Q.ι ⁻¹ᵁ O i) ?_ fun i => ?_
    · rw [← Scheme.Hom.preimage_iSup, ← hQ, Scheme.Opens.ι_preimage_self]
    · have H := hloc i
      rw [← hfac] at H
      change IsImmersion ((h' ⁻¹ᵁ Q.ι ⁻¹ᵁ O i).ι ≫ h' ≫ Q.ι) at H
      rw [← morphismRestrict_ι_assoc] at H
      exact IsImmersion.of_comp _ ((Q.ι ⁻¹ᵁ O i).ι ≫ Q.ι)
  rw [← hfac]
  infer_instance

end AlgebraicGeometry

end
