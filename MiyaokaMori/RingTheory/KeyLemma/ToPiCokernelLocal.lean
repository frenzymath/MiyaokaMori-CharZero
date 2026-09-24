import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.SumDefs

/-! # The cokernel of the comparison map vanishes after localizing away from the maximal ideal

In the same setting: for any family `(x_𝔭)_{𝔭 ∈ MinPrimes(t)}` there are `s ∈ A ∖ q` and `x ∈ B` with
`s·x_𝔭 − x ∈ tB_𝔭 ∩ B` for all `𝔭`. (That is, the cokernel of the comparison map localizes to zero at `q`;
a Chinese remainder theorem.)

References: second paragraph of Stacks 0EAW (the cokernel is supported in `{𝔪}`); 00DT (Chinese remainder
theorem).

**Route** — a "Chinese remainder theorem with denominators" that needs neither the Dedekind ring `B_q`
nor a case split, and does not use normality of `B`:
1. `exists_smul_sub_mem_of_pairwise_sup`: if for all `i ≠ j` some `algebraMap c`, `c ∉ q`, lies in
   `I i ⊔ I j`, then for any family `x` there are `c ∉ q`, `y` with `c·x i − y ∈ I i` for all `i`
   (induction over the finite index set; the usual CRT construction with `c` collecting the denominators).
2. `exists_algebraMap_mem_sup_of_ne`: for distinct `𝔭 ≠ 𝔭' ∈ MinPrimes t`, `𝔭 ⊔ 𝔭'` contains some
   `algebraMap c` with `c ∉ q`. Otherwise a prime `𝔔 ⊇ 𝔭 ⊔ 𝔭'` disjoint from the image of `A∖q`
   exists; then `ker(A → B) < 𝔭 ∩ A < 𝔔 ∩ A ≤ q < 𝔪_A` is a chain of four primes (incomparability
   for the integral extension `A → B`), contradicting `dim A ≤ 2`.
3. `exists_pow_le_contr`: `𝔭^N ≤ contr 𝔭 t` (`𝔭B_𝔭` is the only prime of the noetherian ring `B_𝔭`
   above `tB_𝔭`, so it is the radical of `tB_𝔭` and a power of it lies in `tB_𝔭`).
Then `algebraMap (c^(N+N')) ∈ (𝔭 ⊔ 𝔭')^(N+N') ≤ 𝔭^N ⊔ 𝔭'^N ≤ contr 𝔭 t ⊔ contr 𝔭' t`, and step 1 applies.
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

section CRT

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Chinese remainder theorem with denominators in `A ∖ q` (Stacks 00DT after localizing at `q`,
but stated and proved without localization). If any two of the ideals `I i` become comaximal after
inverting `A ∖ q`, then any family of residues can be matched simultaneously up to a denominator
`c ∉ q`. Proof by induction on the finite index set: given `c, y` for `s`, for a new index `i₀`
decompose `algebraMap (f i₀ i) = a i + b i` (`a i ∈ I i₀`, `b i ∈ I i`) for `i ∈ s`, put
`τ = ∏ f i₀ i`, `e = ∏ b i` (so `e ∈ I i` for `i ∈ s` and `e ≡ τ mod I i₀`), and take
`c' = c·τ`, `y' = τ·y + e·(c·x i₀ − y)`. -/
theorem exists_smul_sub_mem_of_pairwise_sup {ι : Type*} (s : Finset ι) (q : Ideal A) [hq : q.IsPrime]
    (I : ι → Ideal B) (hcop : ∀ i j, i ≠ j → ∃ c : A, c ∉ q ∧ algebraMap A B c ∈ I i ⊔ I j)
    (x : ι → B) :
    ∃ c : A, c ∉ q ∧ ∃ y : B, ∀ i ∈ s, algebraMap A B c * x i - y ∈ I i := by
  classical
  choose! f hf using hcop
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, (Ideal.ne_top_iff_one q).mp hq.ne_top, 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i₀ s hi₀ ih =>
    obtain ⟨c, hc, y, hy⟩ := ih
    have hdec : ∀ i ∈ s, ∃ a b : B, a ∈ I i₀ ∧ b ∈ I i ∧ a + b = algebraMap A B (f i₀ i) := by
      intro i hi
      have hne : i₀ ≠ i := fun h => hi₀ (h ▸ hi)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hf i₀ i hne).2
      exact ⟨a, b, ha, hb, hab⟩
    choose! a b ha hb hab using hdec
    set τ : A := ∏ i ∈ s, f i₀ i with hτdef
    set e : B := ∏ i ∈ s, b i with hedef
    have hτ : τ ∉ q := by
      intro h
      obtain ⟨i, hi, hiq⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact (hf i₀ i (fun h' => hi₀ (h' ▸ hi))).1 hiq
    have he₁ : ∀ i ∈ s, e ∈ I i := by
      intro i hi
      rw [hedef, ← Finset.mul_prod_erase s b hi]
      exact Ideal.mul_mem_right _ _ (hb i hi)
    have he₂ : e - algebraMap A B τ ∈ I i₀ := by
      rw [← Ideal.Quotient.eq, hedef, hτdef, map_prod, map_prod, map_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [← hab i hi, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (ha i hi), zero_add]
    refine ⟨c * τ, fun h => (hq.mem_or_mem h).elim hc hτ,
      algebraMap A B τ * y + e * (algebraMap A B c * x i₀ - y), ?_⟩
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · have : algebraMap A B (c * τ) * x i - (algebraMap A B τ * y + e * (algebraMap A B c * x i - y))
          = -((e - algebraMap A B τ) * (algebraMap A B c * x i - y)) := by
        rw [map_mul]; ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ he₂)
    · have : algebraMap A B (c * τ) * x i - (algebraMap A B τ * y + e * (algebraMap A B c * x i₀ - y))
          = algebraMap A B τ * (algebraMap A B c * x i - y) - e * (algebraMap A B c * x i₀ - y) := by
        rw [map_mul]; ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hy i hi)) (Ideal.mul_mem_right _ _ (he₁ i hi))

end CRT

section Contr

variable {B : Type u} [CommRing B]

/-- For `𝔭` minimal over `(t)`, a power of `𝔭` lies in `contr 𝔭 t = tB_𝔭 ∩ B` (`B` noetherian).
Proof: in the noetherian local ring `R = B_𝔭` every prime `Q ⊇ tR` has `Q ∩ B ⊇ (t)`, `Q ∩ B ≤ 𝔭`
(as `Q ≤ 𝔪_R` and `𝔪_R ∩ B = 𝔭`), so `Q ∩ B = 𝔭` by minimality and `Q = (Q ∩ B)R = 𝔪_R`. Hence
`𝔪_R ≤ rad(tR)` (`Ideal.radical_eq_sInf`), and `𝔪_R^N ≤ tR` for some `N`
(`Ideal.exists_pow_le_of_le_radical_of_fg`); pull back along `B → R` using `𝔭 ≤ 𝔪_R ∩ B`. -/
theorem exists_pow_le_contr [IsNoetherianRing B] {t : B} (𝔭 : PrimeSpectrum B)
    (h𝔭 : 𝔭.asIdeal ∈ (Ideal.span {t}).minimalPrimes) :
    ∃ N : ℕ, 𝔭.asIdeal ^ N ≤ contr 𝔭 t := by
  set R := Localization.AtPrime 𝔭.asIdeal
  set J : Ideal R := Ideal.span {algebraMap B R t} with hJ
  have hrad : IsLocalRing.maximalIdeal R ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun Q ⟨hJQ, hQ⟩ => ?_
    have hQle : Q ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hQ.ne_top
    have hcomap : Q.comap (algebraMap B R) = 𝔭.asIdeal := by
      have hmin : Minimal (fun p : Ideal B => p.IsPrime ∧ Ideal.span {t} ≤ p) 𝔭.asIdeal := h𝔭
      refine hmin.eq_of_le ⟨Ideal.IsPrime.comap _, ?_⟩ ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
        exact hJQ (Ideal.subset_span rfl)
      · calc Q.comap (algebraMap B R) ≤ (IsLocalRing.maximalIdeal R).comap (algebraMap B R) :=
              Ideal.comap_mono hQle
          _ = 𝔭.asIdeal := Localization.AtPrime.under_maximalIdeal
    refine le_of_eq ?_
    calc IsLocalRing.maximalIdeal R = Ideal.map (algebraMap B R) 𝔭.asIdeal :=
          Localization.AtPrime.map_eq_maximalIdeal.symm
      _ = Ideal.map (algebraMap B R) (Q.comap (algebraMap B R)) := by rw [hcomap]
      _ = Q := IsLocalization.map_under 𝔭.asIdeal.primeCompl R Q
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨N, ?_⟩
  have hcm : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = 𝔭.asIdeal :=
    Localization.AtPrime.under_maximalIdeal
  calc 𝔭.asIdeal ^ N = ((IsLocalRing.maximalIdeal R).comap (algebraMap B R)) ^ N := by rw [hcm]
    _ ≤ ((IsLocalRing.maximalIdeal R) ^ N).comap (algebraMap B R) := Ideal.le_comap_pow _ N
    _ ≤ J.comap (algebraMap B R) := Ideal.comap_mono hN

end Contr

variable {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]

omit [IsNoetherianRing A] [IsIntegrallyClosed B] in
/-- Two distinct minimal primes `𝔭 ≠ 𝔭'` of `(t)` become comaximal after inverting `A ∖ q`
(`q ≠ 𝔪_A`, `dim A ≤ 2`). Proof: if `𝔭 ⊔ 𝔭'` met no `algebraMap c` with `c ∉ q`, it would be
disjoint from the submonoid `algebraMap(A ∖ q)`, so some prime `𝔔 ⊇ 𝔭 ⊔ 𝔭'` is disjoint from it
(`Ideal.exists_le_prime_disjoint`), i.e. `𝔔 ∩ A ≤ q`. Since `𝔭' ⊄ 𝔭` (both minimal over `(t)`),
`𝔭 < 𝔔`; incomparability for the integral extension `A → B`
(`Ideal.comap_lt_comap_of_integral_mem_sdiff`, applied to `⊥ < 𝔭` with `t` and to `𝔭 < 𝔔`)
gives the chain of primes `ker(A → B) < 𝔭 ∩ A < 𝔔 ∩ A ≤ q < 𝔪_A`, so `ht 𝔪_A ≥ 3 > dim A`
(`Ideal.height_add_one_le_of_lt_of_isPrime`, `Ideal.height_le_ringKrullDim_of_isPrime`). -/
theorem exists_algebraMap_mem_sup_of_ne (hdim : ringKrullDim A ≤ 2) {t : B} (ht : t ≠ 0)
    (q : Ideal A) [hqP : q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal A) (𝔭 𝔭' : MinPrimes t)
    (hne : 𝔭 ≠ 𝔭') :
    ∃ c : A, c ∉ q ∧ algebraMap A B c ∈ 𝔭.1.asIdeal ⊔ 𝔭'.1.asIdeal := by
  by_contra hcon
  push Not at hcon
  -- The ideal `𝔭 ⊔ 𝔭'` is disjoint from the image of `A ∖ q`.
  have hdisj : Disjoint ((𝔭.1.asIdeal ⊔ 𝔭'.1.asIdeal : Ideal B) : Set B)
      (Algebra.algebraMapSubmonoid B q.primeCompl : Set B) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨c, hc, rfl⟩
    exact hcon c hc hz
  obtain ⟨𝔔, h𝔔, hle, hdisj'⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  have h𝔔q : 𝔔.comap (algebraMap A B) ≤ q := by
    intro c hc
    by_contra hcq
    exact Set.disjoint_left.mp hdisj' hc (Algebra.mem_algebraMapSubmonoid_of_mem (⟨c, hcq⟩ : q.primeCompl))
  -- `𝔭' ⊄ 𝔭`, so there is `z ∈ 𝔔 \ 𝔭`.
  have hnle : ¬ 𝔭'.1.asIdeal ≤ 𝔭.1.asIdeal := by
    intro h
    have hmin : Minimal (fun p : Ideal B => p.IsPrime ∧ Ideal.span {t} ≤ p) 𝔭.1.asIdeal := 𝔭.2
    exact hne (Subtype.ext (PrimeSpectrum.ext (hmin.eq_of_le 𝔭'.2.1 h).symm))
  obtain ⟨z, hz', hz⟩ := SetLike.not_le_iff_exists.mp hnle
  have hz𝔔 : z ∈ 𝔔 := hle (Ideal.mem_sup_right hz')
  have := 𝔭.1.isPrime
  have : (𝔭.1.asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  have : (𝔔.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  have : ((⊥ : Ideal B).comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  -- The chain `ker < 𝔭 ∩ A < 𝔔 ∩ A < 𝔪_A`.
  have h₁ : (⊥ : Ideal B).comap (algebraMap A B) < 𝔭.1.asIdeal.comap (algebraMap A B) :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff bot_le
      ⟨𝔭.2.1.2 (Ideal.mem_span_singleton_self t), by simpa using ht⟩ (Algebra.IsIntegral.isIntegral t)
  have h₂ : 𝔭.1.asIdeal.comap (algebraMap A B) < 𝔔.comap (algebraMap A B) :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff (le_sup_left.trans hle) ⟨hz𝔔, hz⟩
      (Algebra.IsIntegral.isIntegral z)
  have h₃ : 𝔔.comap (algebraMap A B) < IsLocalRing.maximalIdeal A :=
    lt_of_le_of_lt h𝔔q (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q) hq)
  have e₁ := Ideal.height_add_one_le_of_lt_of_isPrime h₁
  have e₂ := Ideal.height_add_one_le_of_lt_of_isPrime h₂
  have e₃ := Ideal.height_add_one_le_of_lt_of_isPrime h₃
  have h3 : (3 : ℕ∞) ≤ (IsLocalRing.maximalIdeal A).height := by
    calc (3 : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
      _ ≤ ((⊥ : Ideal B).comap (algebraMap A B)).height + 1 + 1 + 1 := by
          gcongr; exact zero_le
      _ ≤ (𝔭.1.asIdeal.comap (algebraMap A B)).height + 1 + 1 := by gcongr
      _ ≤ (𝔔.comap (algebraMap A B)).height + 1 := by gcongr
      _ ≤ _ := e₃
  have hm : ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
    (Ideal.height_le_ringKrullDim_of_isPrime).trans hdim
  have := h3.trans (WithBot.coe_le_coe.mp hm)
  exact absurd this (by decide)

set_option linter.unusedSectionVars false in
/-- Proof, by the route `exists_algebraMap_mem_sup_of_ne` (two distinct minimal primes become comaximal after
localizing at `q` — the substance of "the cokernel is supported in `{𝔪}`" in 0EAW) +
`exists_pow_le_contr` (`𝔭^N ≤ contr 𝔭 t`) + the Chinese remainder theorem with denominators
`exists_smul_sub_mem_of_pairwise_sup`. Normality of `B` is not needed (`IsIntegrallyClosed B` is unused).
Edge case: `MinPrimes t` empty (`t` a unit) ⇒ the empty induction base of the CRT gives `s = 1`, `x = 0`.
(`[IsIntegrallyClosed B]` is kept in the statement for consistency with the user `ToPiFiniteLength`; it is
not used in the proof.) -/
theorem exists_smul_sub_mem_contr (hdim : ringKrullDim A ≤ 2) {t : B} (ht : t ≠ 0)
    (q : Ideal A) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal A) (x : MinPrimes t → B) :
    ∃ s : A, s ∉ q ∧ ∃ y : B, ∀ 𝔭 : MinPrimes t, algebraMap A B s * x 𝔭 - y ∈ contr 𝔭.1 t := by
  classical
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Finite (MinPrimes t) := by
    have := (Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {t})).to_subtype
    exact Finite.of_injective
      (fun 𝔭 : MinPrimes t => (⟨𝔭.1.asIdeal, 𝔭.2⟩ : (Ideal.span {t}).minimalPrimes))
      (fun x y h => Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val h)))
  have := Fintype.ofFinite (MinPrimes t)
  have hcop : ∀ 𝔭 𝔭' : MinPrimes t, 𝔭 ≠ 𝔭' →
      ∃ c : A, c ∉ q ∧ algebraMap A B c ∈ contr 𝔭.1 t ⊔ contr 𝔭'.1 t := by
    intro 𝔭 𝔭' hne
    obtain ⟨N, hN⟩ := exists_pow_le_contr 𝔭.1 𝔭.2
    obtain ⟨N', hN'⟩ := exists_pow_le_contr 𝔭'.1 𝔭'.2
    obtain ⟨c, hc, hmem⟩ := exists_algebraMap_mem_sup_of_ne hdim ht q hq 𝔭 𝔭' hne
    refine ⟨c ^ (N + N'), fun h => hc (‹q.IsPrime›.mem_of_pow_mem _ h), ?_⟩
    rw [map_pow]
    exact (sup_le_sup hN hN') (Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_mem_pow hmem _))
  obtain ⟨c, hc, y, hy⟩ :=
    exists_smul_sub_mem_of_pairwise_sup Finset.univ q (fun 𝔭 : MinPrimes t => contr 𝔭.1 t) hcop x
  exact ⟨c, hc, y, fun 𝔭 => hy 𝔭 (Finset.mem_univ _)⟩

end KeyLemma

end
