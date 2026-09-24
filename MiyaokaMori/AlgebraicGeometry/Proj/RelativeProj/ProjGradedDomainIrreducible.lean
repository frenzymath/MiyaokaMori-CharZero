import MiyaokaMori.Prelude

/-! # Proj of a graded domain is irreducible

The Proj of a graded domain (with a nonzero homogeneous element of positive degree) is irreducible:
the zero ideal is a generic point. Used for the integrality of `Y_k^GG` (Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Proj.irreducibleSpace_of_isDomain {A σ : Type*} [CommRing A] [IsDomain A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (h : ∃ (m : ℕ) (f : A), 0 < m ∧ f ∈ 𝒜 m ∧ f ≠ 0) :
    IrreducibleSpace (AlgebraicGeometry.Proj 𝒜) := by
  let p : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := Ideal.isPrime_bot
      not_irrelevant_le := by
        intro hle
        obtain ⟨m, f, hm, hf, hf0⟩ := h
        have hfm : f ∈ (HomogeneousIdeal.irrelevant 𝒜 : Set A) := by
          exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hm hf
        have : f ∈ (⊥ : HomogeneousIdeal 𝒜) := hle hfm
        exact hf0 (show f = 0 from this) }
  have hp : closure ({p} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    apply (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := 𝒜) p q).mp
    change p.asHomogeneousIdeal ≤ q.asHomogeneousIdeal
    exact bot_le
  exact (irreducibleSpace_def _).mpr <| by
    change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
    rw [← hp]
    exact isIrreducible_singleton.closure

end
