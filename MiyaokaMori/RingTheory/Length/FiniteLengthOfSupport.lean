import MiyaokaMori.Prelude

/-! # Finite length of a module supported at the closed point

Let `A` be a Noetherian local ring and `N` a finite `A`-module. If for every non-maximal prime `q` every
element of `N` is annihilated by some `s ∉ q` (i.e. `N_q = 0`), then `N` has finite length.

Reference: Stacks 00L5 (algebra-lemma-support-point: a finite module supported in `{𝔪}` has finite length).
-/

set_option autoImplicit false

universe u


noncomputable section

namespace KeyLemma

end KeyLemma

/-- Proof (the standard proof of Stacks 00L5): let `I = Ann(N)`. `N` is an `A/I`-module, and its `A`-submodules
are its `A/I`-submodules (`Module.quotientAnnihilator`, `LinearMap.isArtinian_iff_of_bijective`). Every prime
`J` of `A/I` pulls back to a prime `P ⊇ I` of `A`; by `Supp N = V(I)` (Stacks 00L2,
`Module.mem_support_iff_of_finite`) and the hypothesis (`Module.notMem_support_iff'`), `P = 𝔪`, so `J = 𝔪/I`
is maximal, i.e. `dim A/I = 0`; Noetherian + zero-dimensional ⇒ Artinian (Stacks 00KH,
`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`); a finite module over an Artinian ring is Artinian, and
`Module.length_ne_top` (Artinian + Noetherian ⇒ finite length) concludes.

Alternative: `N` is Noetherian, so it has a prime filtration `0 = N_0 ⊂ … ⊂ N_k = N` with
`N_i/N_{i−1} ≅ A/p_i` (Stacks 00L0; Mathlib `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`);
each `p_i ∈ Supp N`, so `p_i = 𝔪` by the hypothesis, `A/𝔪` has length `1`, and length is additive.
Edge cases: `N = 0`; `A` a field (no non-maximal primes, the hypothesis is vacuous, `N` is
finite-dimensional). -/
theorem Module.length_ne_top_of_forall_exists_smul_eq_zero {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (h : ∀ q : Ideal A, q.IsPrime → q ≠ IsLocalRing.maximalIdeal A → ∀ m : N, ∃ s : A, s ∉ q ∧ s • m = 0) :
    Module.length A N ≠ ⊤ := by
  classical
  -- `I := Ann(N)`; `N` is a module over `A ⧸ I`, finite, with the same submodules.
  set I : Ideal A := Module.annihilator A N with hI
  let : Module (A ⧸ I) N := Module.quotientAnnihilator
  have : IsScalarTower A (A ⧸ I) N := Module.IsTorsionBySet.isScalarTower _
  -- Every prime of `A ⧸ I` is maximal: its preimage `P ⊇ I` is a prime of `A` in `Supp N`,
  -- hence `P = 𝔪` by the hypothesis (Stacks 00L2: `Supp N = V(Ann N)` for finite `N`).
  have hdim : Ring.KrullDimLE 0 (A ⧸ I) := by
    rw [Ring.krullDimLE_zero_iff]
    intro J hJ
    have hP : (J.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ J
    have hIP : I ≤ J.comap (Ideal.Quotient.mk I) := by
      intro x hx
      show Ideal.Quotient.mk I x ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hPm : J.comap (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal A := by
      by_contra hne
      have hmem : (⟨_, hP⟩ : PrimeSpectrum A) ∈ Module.support A N :=
        Module.mem_support_iff_of_finite.mpr hIP
      have hnot : (⟨_, hP⟩ : PrimeSpectrum A) ∉ Module.support A N :=
        Module.notMem_support_iff'.mpr (h _ hP hne)
      exact hnot hmem
    have hmax : (J.comap (Ideal.Quotient.mk I)).IsMaximal := by
      rw [hPm]; exact IsLocalRing.maximalIdeal.isMaximal A
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective hmax with htop | hmax'
    · rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at htop
      exact absurd htop hJ.ne_top
    · rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmax'
  -- `A ⧸ I` is Noetherian of dimension 0, hence Artinian (Stacks 00KH); `N` is finite over it.
  have : IsArtinianRing (A ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have : Module.Finite (A ⧸ I) N := Module.Finite.of_restrictScalars_finite A (A ⧸ I) N
  have : IsArtinian (A ⧸ I) N := inferInstance
  -- `A`-submodules and `A ⧸ I`-submodules of `N` coincide, so `N` is Artinian over `A`.
  have : IsArtinian A N :=
    ((Module.isTorsionBySet_annihilator A N).semilinearMap.isArtinian_iff_of_bijective
      Function.bijective_id).mpr this
  have : IsNoetherian A N := inferInstance
  exact Module.length_ne_top

namespace KeyLemma

end KeyLemma

end
