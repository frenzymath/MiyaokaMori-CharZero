import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.SumDefs

/-! # The kernel of the comparison map vanishes after localizing away from the maximal ideal

`A` Noetherian local with `dim A ≤ 2`, `B` a normal domain finite over `A`, `t ≠ 0`, `q ≠ 𝔪_A` a prime of
`A`. If `x ∈ B` lies in every `tB_𝔭 ∩ B` (`𝔭 ∈ MinPrimes(t)`), then there is `s ∈ A ∖ q` with `s·x ∈ tB`.
(That is, the kernel of the comparison map `B/t → ⊕ B/(tB_𝔭 ∩ B)` localizes to zero at `q`.)

References: second paragraph of Stacks 0EAW (the kernel is supported in `{𝔪}`); 034O / 031T (no
embedded components for principal ideals of a Noetherian normal domain — only the Dedekind case after
localizing at `q` would be needed). The actual proof uses only dimension and incomparability for integral
extensions (Stacks 00GT), not normality: see the docstring of `exists_smul_mem_span_of_forall_mem_contr`.
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]

omit [IsNoetherianRing A] [IsIntegrallyClosed B] in
/-- Auxiliary: `B` a domain integral over `A`; `A` local with `dim A ≤ 2`; `P` a prime of `B` containing a
nonzero element `t` with `P ∩ A ⊆ q ⊊ 𝔪_A`; then `P` is a minimal prime of `(t)`.
Proof: if a prime `Q` satisfies `t ∈ Q ⊊ P`, then `⊥ < Q < P` (`Q ≠ ⊥` since `t ∈ Q`, `t ≠ 0`), and
incomparability (`Ideal.IsIntegral.comap_lt_comap`) gives the strict chain
`⊥∩A < Q∩A < P∩A ≤ q < 𝔪_A` in `A`, of length `3 > dim A`. -/
theorem isMinimalPrime_of_comap_le (hdim : ringKrullDim A ≤ 2) {t : B} (ht : t ≠ 0)
    (q : Ideal A) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal A)
    (P : Ideal B) [hP : P.IsPrime] (htP : t ∈ P) (hPq : P.comap (algebraMap A B) ≤ q) :
    (Ideal.span {t}).IsMinimalPrime P := by
  refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem P).mpr htP⟩, ?_⟩
  rintro Q ⟨hQ, htQ⟩ hQP
  by_contra hPQ
  have hQP' : Q < P := lt_of_le_not_ge hQP hPQ
  have hQ0 : (⊥ : Ideal B) < Q := by
    refine bot_lt_iff_ne_bot.mpr fun h => ht ?_
    have : t ∈ Q := htQ (Ideal.mem_span_singleton_self t)
    rw [h] at this
    exact (Submodule.mem_bot B).mp this
  have hqm : q < IsLocalRing.maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q) hq
  have h0 : (⊥ : Ideal B).comap (algebraMap A B) < Q.comap (algebraMap A B) :=
    Ideal.IsIntegral.comap_lt_comap hQ0
  have h1 : Q.comap (algebraMap A B) < P.comap (algebraMap A B) :=
    Ideal.IsIntegral.comap_lt_comap hQP'
  have h2 : P.comap (algebraMap A B) < IsLocalRing.maximalIdeal A := lt_of_le_of_lt hPq hqm
  -- the strict chain `⊥∩A < Q∩A < P∩A < 𝔪_A` in the prime spectrum
  let p0 : PrimeSpectrum A := ⟨(⊥ : Ideal B).comap (algebraMap A B), Ideal.IsPrime.comap _⟩
  let p1 : PrimeSpectrum A := ⟨Q.comap (algebraMap A B), Ideal.IsPrime.comap _⟩
  let p2 : PrimeSpectrum A := ⟨P.comap (algebraMap A B), Ideal.IsPrime.comap _⟩
  let p3 : PrimeSpectrum A := ⟨IsLocalRing.maximalIdeal A, inferInstance⟩
  let c : LTSeries (PrimeSpectrum A) :=
    (((RelSeries.singleton _ p0).snoc p1 (by rw [RelSeries.last_singleton]; exact (PrimeSpectrum.asIdeal_lt_asIdeal p0 p1).mp h0)).snoc p2
      (by rw [RelSeries.last_snoc]; exact (PrimeSpectrum.asIdeal_lt_asIdeal p1 p2).mp h1)).snoc p3 (by rw [RelSeries.last_snoc]; exact (PrimeSpectrum.asIdeal_lt_asIdeal p2 p3).mp h2)
  have hlen : c.length = 3 := rfl
  have := Order.LTSeries.length_le_krullDim c
  rw [hlen] at this
  have h3 : ((3 : ℕ) : WithBot ℕ∞) ≤ 2 := le_trans this hdim
  exact absurd h3 (by decide)

set_option linter.unusedSectionVars false in
/-- Proof (no normality needed, only dimension): suppose the conclusion fails. Let `I := (tB : x) = {b | b·x ∈ tB}`
and `S :=` the image of `A ∖ q` in `B`; the assumption says `I ∩ S = ∅`, so there is a prime `P ⊇ I`
disjoint from `S` (`Ideal.exists_le_prime_disjoint`), hence `P ∩ A ⊆ q`, and `t ∈ I ⊆ P`. By
`isMinimalPrime_of_comap_le` (incomparability + `dim A ≤ 2`), `P` is a minimal prime of `(t)`, so the
hypothesis gives `x ∈ tB_P ∩ B`, i.e. there is `u ∉ P` with `u·x ∈ tB`
(`IsLocalization.algebraMap_mem_map_algebraMap_iff`); then `u ∈ I ⊆ P`, a contradiction.
(Instead of passing through the Dedekind domain `B_q`, this uses directly the skeleton "`(x) ⊆ (t)` can be
checked locally at maximal ideals".)
Edge cases: `t` a unit ⇒ `MinPrimes t` is empty, but the conclusion still follows from the argument above
(then `(tB : x) = B` cannot be disjoint from `S`, and the assumption is immediately contradictory);
`x = 0 ⇒ s = 1`.
Note: the hypotheses `IsNoetherianRing A`, `IsIntegrallyClosed B` are not used in this proof; they are
kept for consistency with the `variable` line shared with the neighbouring lemmas. -/
theorem exists_smul_mem_span_of_forall_mem_contr (hdim : ringKrullDim A ≤ 2) {t : B} (ht : t ≠ 0)
    (q : Ideal A) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal A) (x : B)
    (hx : ∀ 𝔭 : MinPrimes t, x ∈ contr 𝔭.1 t) :
    ∃ s : A, s ∉ q ∧ algebraMap A B s * x ∈ Ideal.span {t} := by
  by_contra hcon
  -- I := (tB : x)
  set I : Ideal B := (Ideal.span {t}).colon {x} with hI
  have hmemI : ∀ b : B, b ∈ I ↔ b * x ∈ Ideal.span {t} := fun b => by
    rw [hI, Submodule.mem_colon_singleton, smul_eq_mul]
  -- S := image of A∖q
  set S : Submonoid B := q.primeCompl.map (algebraMap A B) with hS
  have hdisj : Disjoint (I : Set B) S := by
    rw [Set.disjoint_left]
    intro b hb hbS
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hbS
    exact hcon ⟨s, hs, (hmemI _).mp hb⟩
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint I S hdisj
  have htI : t ∈ I := (hmemI t).mpr (Ideal.mem_span_singleton'.mpr ⟨x, mul_comm x t⟩)
  have htP : t ∈ P := hIP htI
  have hPq : P.comap (algebraMap A B) ≤ q := by
    intro a ha
    by_contra haq
    exact Set.disjoint_left.mp hPS (Ideal.mem_comap.mp ha) (Submonoid.mem_map.mpr ⟨a, haq, rfl⟩)
  have hmin : P ∈ (Ideal.span {t}).minimalPrimes :=
    isMinimalPrime_of_comap_le hdim ht q hq P htP hPq
  have hxP := hx ⟨⟨P, hP⟩, hmin⟩
  -- unfold `contr`: `x/1 ∈ (t) B_P ⇒ ∃ u ∉ P, u * x ∈ (t)`
  simp only [contr, Ideal.mem_comap] at hxP
  rw [← Set.image_singleton, ← Ideal.map_span,
    IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl] at hxP
  obtain ⟨u, hu, hux⟩ := hxP
  exact hu (hIP ((hmemI u).mpr hux))

end KeyLemma

end
