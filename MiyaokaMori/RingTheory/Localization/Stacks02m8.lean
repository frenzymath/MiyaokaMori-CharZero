import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Localization.Stacks02m6
import MiyaokaMori.RingTheory.Localization.AssociatedPrimesComapSurjective
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-! # Stacks 02M8: the ring `R/Ann M` has no embedded primes

Stacks 02M8: `R` Noetherian, `M` finite without embedded associated primes, `I = Ann M`; then the ring `R/I`
has no embedded primes.

Reference: Stacks 02M8 (algebra-lemma-no-embedded-primes-endos), citing 00L2.

Proof (as formalized; shorter than the Stacks argument, every step in Mathlib).
Write `I = Ann_R M`. By `Module.hasNoEmbeddedPrimes_iff_of_surjective` (base change along the
surjection `R → R/I`) it suffices to show that the `R`-module `R/I` has no embedded primes.
1. `Ass_R(R/I) ⊆ Ass_R(M)`: pick generators `s : Fin n → M` of `M`; the `R`-linear map
   `R → Mⁿ`, `r ↦ (r • s i)_i` has kernel exactly `I`, so it descends to an injective map
   `R/I ↪ Mⁿ`, and `Ass(R/I) ⊆ Ass(Mⁿ) = Ass(M)` (`associatedPrimes.subset_of_injective`,
   `associatedPrimes.prod` iterated as `associatedPrimes_pi_fin_subset`).
2. Every `P ∈ Ass_R(R/I)` is a minimal prime of `I`: `I ≤ P` (`IsAssociatedPrime.annihilator_le`
   applied to `P ∈ Ass(M)`), so `P` contains a minimal prime `P₀` of `I`
   (`Ideal.exists_minimalPrimes_le`); `P₀ ∈ Ass(M)` (`Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`,
   Stacks 00L2 / 02M8's use of it), and `hM` gives `P₀ = P`.
3. Hence for `P ≤ Q` in `Ass_R(R/I)`, both equal minimal primes of `I` below `Q`, and `hM` on
   `P₀ ≤ Q` gives `P₀ = Q`, so `P = Q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Associated primes of a finite product `Fin n → M` are those of `M` (for `n = 0` the product is
zero and has no associated primes, so we only get `⊆`). -/
theorem associatedPrimes_pi_fin_subset (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) : associatedPrimes R (Fin n → M) ⊆ associatedPrimes R M := by
  induction n with
  | zero =>
    rw [associatedPrimes.eq_empty_of_subsingleton]
    exact Set.empty_subset _
  | succ n ih =>
    rw [← LinearEquiv.AssociatedPrimes.eq (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => M)),
      associatedPrimes.prod]
    exact Set.union_subset (le_refl _) ih

/-- For `M` finite over `R` with `I = Ann_R M`, `Ass_R (R ⧸ I) ⊆ Ass_R M` (via `R/I ↪ Mⁿ`). -/
theorem associatedPrimes_quotient_annihilator_subset (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    associatedPrimes R (R ⧸ Module.annihilator R M) ⊆ associatedPrimes R M := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let f : R →ₗ[R] (Fin n → M) := LinearMap.pi fun i => LinearMap.toSpanSingleton R M (s i)
  have hker : Module.annihilator R M = LinearMap.ker f := by
    ext r
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      funext i
      simp [f, Module.mem_annihilator.mp h]
    · intro h
      rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
      rintro ⟨_, i, rfl⟩
      have := congrFun h i
      simpa [f] using this
  have hinj : Function.Injective ((Module.annihilator R M).liftQ f hker.le) :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ hker)
  exact (associatedPrimes.subset_of_injective hinj).trans (associatedPrimes_pi_fin_subset R M n)

/- Stacks 02M8: `R` Noetherian, `M` finite without embedded associated primes, `I = Ann M`; then the ring
   `R/I` (as a module over itself) has no embedded primes. -/

theorem Module.hasNoEmbeddedPrimes_quotient_annihilator (R M : Type u) [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.HasNoEmbeddedPrimes R M) :
    Module.HasNoEmbeddedPrimes (R ⧸ Module.annihilator R M) (R ⧸ Module.annihilator R M) := by
  set I := Module.annihilator R M with hI
  have hsmul : ∀ (a : R) (n : R ⧸ I), a • n = Ideal.Quotient.mk I a • n := by
    intro a n
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective n
    rfl
  rw [← Module.hasNoEmbeddedPrimes_iff_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective hsmul]
  have hsub := associatedPrimes_quotient_annihilator_subset R M
  -- every associated prime of `R/I` equals a minimal prime of `I`
  have key : ∀ P ∈ associatedPrimes R (R ⧸ I), ∀ Q ∈ associatedPrimes R M, P ≤ Q → P = Q := by
    intro P hP Q hQ hPQ
    have hPM : P ∈ associatedPrimes R M := hsub hP
    have hIP : I ≤ P := by
      rw [hI, ← Submodule.annihilator_top]
      exact IsAssociatedPrime.annihilator_le hPM
    have : P.IsPrime := hPM.isPrime
    obtain ⟨P₀, hP₀, hP₀P⟩ := Ideal.exists_minimalPrimes_le hIP
    have hP₀M : P₀ ∈ associatedPrimes R M := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hP₀
    have h1 : P₀ = P := hM P₀ hP₀M P hPM hP₀P
    have h2 : P₀ = Q := hM P₀ hP₀M Q hQ (h1 ▸ hPQ)
    exact h1.symm.trans h2
  intro P hP Q hQ hPQ
  exact key P hP Q (hsub hQ) hPQ

end
