import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup

/-!
# Finite support of an actual point-blowup sequence

In the proof of Corollary 4.3 of the paper (§4), a general fibre avoids the
finitely many blowup centres. The inductive sequence already retains the actual centres and
their morphisms to the original surface. These lemmas extract a finite set of
their images, and then a finite set on the base of an actual ruling.

Only the permitted set of centres is enlarged or replaced; the scheme, the
composite morphism, and every actual blowup remain the same. No isomorphism,
properness, closedness of the images on the base, or fibre geometry is inferred
in this file. Those are separate geometric steps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Classical

namespace MiyaokaMori.Statement.IsPointBlowupSequenceOver

universe u

variable {W S : Scheme.{u}} {β : S ⟶ W}

/-- Enlarging the allowed set preserves the same actual point-blowup sequence. -/
theorem mono {A B : Set W} (hβ : IsPointBlowupSequenceOver W A β) (hAB : A ⊆ B) :
    IsPointBlowupSequenceOver W B β := by
  induction hβ with
  | id => exact .id
  | cons f b previous centre closed hcentre blowup ih =>
    exact .cons f b ih centre closed (hAB hcentre) blowup

/-- All centres of the same sequence map into a finite subset of its permitted set. -/
theorem exists_finset_centres {A : Set W} (hβ : IsPointBlowupSequenceOver W A β) :
    ∃ K : Finset W, (K : Set W) ⊆ A ∧ IsPointBlowupSequenceOver W (K : Set W) β := by
  induction hβ with
  | id =>
    exact ⟨∅, by simpa only [Finset.coe_empty] using Set.empty_subset A, .id⟩
  | cons f b previous centre closed hcentre blowup ih =>
    obtain ⟨K, hK, hprevious⟩ := ih
    refine ⟨insert (f centre) K, ?_, .cons f b ?_ centre closed ?_ blowup⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · exact hx.symm ▸ hcentre
      · exact hK hx
    · exact hprevious.mono (by
        intro x hx
        exact Finset.mem_insert_of_mem hx)
    · exact Finset.mem_insert_self _ _

/-- The centres lie over a finite set on the base of any given ruling. -/
theorem exists_finset_base {A : Set W} (hβ : IsPointBlowupSequenceOver W A β)
    {C : Scheme.{u}} (π : W ⟶ C) :
    ∃ T : Finset C, IsPointBlowupSequenceOver W (π ⁻¹' (T : Set C)) β := by
  obtain ⟨K, _, hK⟩ := hβ.exists_finset_centres
  refine ⟨K.image π, hK.mono ?_⟩
  intro x hx
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Outside a finite set of base points every centre avoids that entire original fibre. -/
theorem exists_finset_fibre_avoidance {A : Set W}
    (hβ : IsPointBlowupSequenceOver W A β) {C : Scheme.{u}} (π : W ⟶ C) :
    ∃ T : Finset C, ∀ y : C, y ∉ T →
      IsPointBlowupSequenceOver W {w : W | π w ≠ y} β := by
  obtain ⟨T, hT⟩ := hβ.exists_finset_base π
  refine ⟨T, fun y hy ↦ hT.mono ?_⟩
  intro w hw hwy
  exact hy (hwy ▸ hw)

end MiyaokaMori.Statement.IsPointBlowupSequenceOver
