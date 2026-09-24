import MiyaokaMori.Prelude
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Length bookkeeping for Stacks 0AGT

Four small facts about `Module.length` used to assemble the length inequality of Stacks 0AGT:
* `Module.length_lt_of_notMem`: a proper submodule (missing a given element) of a finite-length
  module has strictly smaller length;
* `Module.length_le_length_quotient_of_surjective`: a quotient of `R/J` has length `≤ ℓ(R/J)`;
* `Module.length_quotient_map_le_of_surjective`: for a surjective ring map `φ : A → R`,
  `ℓ_R(R/I·R) ≤ ℓ_A(A/I)`;
* `Module.length_quotient_ne_top_of_maximalIdeal_pow_le`: `𝔪ⁿ ⊆ I` in a Noetherian local ring
  `A` ⇒ `ℓ_A(A/I) < ∞` (Hopkins–Levitzki: `A/I` has Krull dimension `0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

noncomputable section

namespace Module

/-- A submodule missing some element of a finite-length module has strictly smaller length:
`ℓ(M) = ℓ(N) + ℓ(M/N)` and `M/N ≠ 0`. -/
theorem length_lt_of_notMem {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hfin : Module.length R M ≠ ⊤) {m : M} (hm : m ∉ N) :
    Module.length R N < Module.length R M := by
  have hadd := Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.subtype_injective N)
    (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
  have hN : Module.length R N ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (Module.length_le_of_injective N.subtype (Submodule.subtype_injective N))
  have : Nontrivial (M ⧸ N) :=
    ⟨⟨Submodule.Quotient.mk m, 0, fun h => hm ((Submodule.Quotient.mk_eq_zero N).1 h)⟩⟩
  have hpos : 0 < Module.length R (M ⧸ N) := Module.length_pos
  rw [hadd]
  calc Module.length R N = Module.length R N + 0 := (add_zero _).symm
    _ < Module.length R N + Module.length R (M ⧸ N) := (ENat.add_lt_add_iff_left hN).2 hpos

/-- If `f : R → Q` is a surjective linear map killing the ideal `J`, then `ℓ(Q) ≤ ℓ(R/J)`. -/
theorem length_le_length_quotient_of_surjective {R : Type u} {Q : Type v} [CommRing R]
    [AddCommGroup Q] [Module R Q] (f : R →ₗ[R] Q) (hf : Function.Surjective f) (J : Ideal R)
    (hJ : J ≤ LinearMap.ker f) : Module.length R Q ≤ Module.length R (R ⧸ J) :=
  Module.length_le_of_surjective (J.liftQ f hJ) fun q => by
    obtain ⟨r, rfl⟩ := hf q
    exact ⟨Submodule.Quotient.mk r, Submodule.liftQ_apply _ _ _⟩

/-- For a surjective ring map `φ : A → R` and an ideal `I ⊆ A`: `ℓ_R(R/I·R) ≤ ℓ_A(A/I)`.
Proof: `R/I·R` is an `A`-module through `φ`, its `A`-length equals its `R`-length
(`Module.length_eq_of_surjective`), and `A/I → R/I·R` is a surjective `A`-linear map. -/
theorem length_quotient_map_le_of_surjective {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    (φ : A →+* R) (hφ : Function.Surjective φ) (I : Ideal A) :
    Module.length R (R ⧸ I.map φ) ≤ Module.length A (A ⧸ I) := by
  let _ : Algebra A R := φ.toAlgebra
  have h1 : Module.length A (R ⧸ I.map φ) = Module.length R (R ⧸ I.map φ) :=
    Module.length_eq_of_surjective (S := A) hφ
  rw [← h1]
  refine Module.length_le_of_surjective
    (Ideal.quotientMapₐ (I.map φ) (Algebra.ofId A R) Ideal.le_comap_map).toLinearMap ?_
  intro q
  obtain ⟨y, hy⟩ := Ideal.quotientMap_surjective (I := I.map φ) (J := I)
    (f := (Algebra.ofId A R : A →+* R)) (H := Ideal.le_comap_map) hφ q
  exact ⟨y, hy⟩

/-- In a Noetherian local ring `A`, if `𝔪ⁿ ⊆ I` then `A/I` has finite length.
Proof: every prime `P` of `A/I` pulls back to a prime `⊇ I ⊇ 𝔪ⁿ`, hence `⊇ 𝔪`, hence `= 𝔪`; so
`P = 𝔪·(A/I)` is maximal, `A/I` has Krull dimension `0`, and is Artinian by Hopkins–Levitzki
(`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`); then `Module.length_ne_top`. -/
theorem length_quotient_ne_top_of_maximalIdeal_pow_le {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) (h : IsLocalRing.maximalIdeal A ^ n ≤ I) :
    Module.length A (A ⧸ I) ≠ ⊤ := by
  have hdim : Ring.KrullDimLE 0 (A ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have hI : I ≤ P.comap (Ideal.Quotient.mk I) := fun a ha => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact P.zero_mem
    have hcomap : (P.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ _
    have hm : IsLocalRing.maximalIdeal A ≤ P.comap (Ideal.Quotient.mk I) :=
      hcomap.le_of_pow_le (h.trans hI)
    have heq : P.comap (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal A :=
      ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hcomap.ne_top hm).symm
    have hmap := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective P
    have hPeq : P = (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) := by
      rw [← heq, hmap]
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal.isMaximal A) with htop | hmax
    · exact absurd (hPeq.trans htop) hP.ne_top
    · exact hPeq ▸ hmax
  have : IsArtinianRing (A ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ I) (M := A ⧸ I) (by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

end Module

end
