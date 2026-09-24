import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.EmbeddedPartCoherent

/-! # Commutative algebra for regular meromorphic sections (Stacks 02OZ)

Commutative algebra for Stacks 02OZ / 0EMI, all elementary:

* `Ideal.exists_common_fraction_of_minimalPrimes` (a Chinese-remainder argument): `A` a commutative
  ring, `P i` (`i ∈ t`, `t` finite, `P` injective on `t`) primes each minimal over `⊥`, and for each `i` a
  "unit" `a i / b i` (`a i, b i ∉ P i`). Then there are `a₀ b₀ ∈ A`, both outside every `P i`, with
  `a₀ / b₀ = a i / b i` in `A_{P i}` for every `i ∈ t` (spelled `∃ c ∉ P i, c * (a₀ * b i) = c * (b₀ * a i)`).
  Proof: distinct minimal primes are incomparable, so for `p ≠ p'` pick `x ∈ p' \ p`; `e p := ∏_{p' ≠ p} x`
  lies in every `p' ≠ p` and not in `p`. Since `p` is minimal over `⊥`, every element of `p` is
  nilpotent in `A_p` (`Ideal.exists_mul_pow_mem_of_mem_minimalPrimes'` with `I = ⊥`): for `p' ≠ p` there
  are `y ∉ p`, `n` with `y * e p' ^ n = 0`. With `N + 1` a common exponent, `a₀ := ∑ e p ^ (N+1) * a p`,
  `b₀ := ∑ e p ^ (N+1) * b p`; in `A_p` all terms with `p' ≠ p` die (multiply by `t := ∏ y`), leaving
  `e p ^ (N+1) a p / e p ^ (N+1) b p = a p / b p`, and `a₀, b₀ ∉ p` since `a₀ ≡ e p ^ (N+1) a p mod p`.
* `IsLocalization.colon_bot_singleton_map`: `Ann_S(m/1) = S⁻¹ Ann_A(m)` for a localization `S` of `A`.
* `IsLocalization.AtPrime.maximalIdeal_mem_associatedPrimes_of_eq_radical`: if `q = rad(Ann_A m)` for
  some `m ∈ A` (i.e. `q ∈ Ass_A(A)`), then `q A_q = rad(Ann_{A_q}(m/1))`, so `q A_q ∈ Ass_{A_q}(A_q)`
  (Stacks 05BV / 00LD bookkeeping; uses `IsLocalization.map_radical`).
* `IsLocalization.AtPrime.maximalIdeal_mem_associatedPrimes_of_mem_minimalPrimes`: if `q` is a minimal
  prime of `A`, then `q A_q = rad(0) = rad(Ann(1))`, so `q A_q ∈ Ass_{A_q}(A_q)`
  (`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`).

Source: Stacks 02OZ, 0EMI, 00LD; standard.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

noncomputable section

/-- Common fraction for finitely many units at minimal primes (see the module docstring); the primes are
indexed by a finite set `t` through an injective map `P`. -/
theorem Ideal.exists_common_fraction_of_minimalPrimes {A : Type*} [CommRing A] {ι : Type*}
    (t : Finset ι) (P : ι → PrimeSpectrum A) (hP : Set.InjOn P t)
    (hs : ∀ i ∈ t, (P i).asIdeal ∈ (⊥ : Ideal A).minimalPrimes)
    (a b : ι → A) (ha : ∀ i ∈ t, a i ∉ (P i).asIdeal) (hb : ∀ i ∈ t, b i ∉ (P i).asIdeal) :
    ∃ a₀ b₀ : A, ∀ i ∈ t, a₀ ∉ (P i).asIdeal ∧ b₀ ∉ (P i).asIdeal ∧
      ∃ c ∉ (P i).asIdeal, c * (a₀ * b i) = c * (b₀ * a i) := by
  classical
  -- distinct minimal primes are incomparable
  have hinc : ∀ i ∈ t, ∀ i' ∈ t, i' ≠ i → ∃ x, x ∈ (P i').asIdeal ∧ x ∉ (P i).asIdeal := by
    intro i hi i' hi' hne
    by_contra hcon
    push Not at hcon
    have hle : (P i').asIdeal ≤ (P i).asIdeal := hcon
    have hge : (P i).asIdeal ≤ (P i').asIdeal := (hs i hi).2 ⟨(P i').isPrime, bot_le⟩ hle
    exact hne (hP hi' hi (PrimeSpectrum.ext (le_antisymm hle hge)))
  choose! x hx hx' using hinc
  -- `e i ∈ P i'` for `i' ≠ i`, `e i ∉ P i`
  let e : ι → A := fun i => ∏ i' ∈ t.erase i, x i i'
  have he_mem : ∀ i ∈ t, ∀ i' ∈ t, i' ≠ i → e i ∈ (P i').asIdeal := by
    intro i hi i' hi' hne
    have hmem : i' ∈ t.erase i := Finset.mem_erase.mpr ⟨hne, hi'⟩
    show ∏ i'' ∈ t.erase i, x i i'' ∈ (P i').asIdeal
    rw [← Finset.mul_prod_erase (t.erase i) (x i) hmem]
    exact (P i').asIdeal.mul_mem_right _ (hx i hi i' hi' hne)
  have he_notMem : ∀ i ∈ t, e i ∉ (P i).asIdeal := by
    intro i hi hmem
    obtain ⟨i', hi', hcon⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (P i).isPrime)).mp hmem
    have hi'' := Finset.mem_erase.mp hi'
    exact hx' i hi i' hi''.2 hi''.1 hcon
  -- nilpotency of `e i'` in `A_{P i}` for `i' ≠ i`
  have hnil : ∀ i ∈ t, ∀ i' ∈ t, i' ≠ i → ∃ y, y ∉ (P i).asIdeal ∧ ∃ n : ℕ, y * e i' ^ n = 0 := by
    intro i hi i' hi' hne
    obtain ⟨y, hy, n, hn⟩ := Ideal.exists_mul_pow_mem_of_mem_minimalPrimes' (hs i hi)
      (he_mem i' hi' i hi (Ne.symm hne))
    exact ⟨y, hy, n, (Ideal.mem_bot).mp hn⟩
  choose! y hy n hn using hnil
  let N : ℕ := (t ×ˢ t).sup fun pp => n pp.1 pp.2
  have hN : ∀ i ∈ t, ∀ i' ∈ t, i' ≠ i → y i i' * e i' ^ N = 0 := by
    intro i hi i' hi' hne
    have hmem : (i, i') ∈ t ×ˢ t := Finset.mem_product.mpr ⟨hi, hi'⟩
    have hle : n i i' ≤ N := Finset.le_sup (f := fun pp : ι × ι => n pp.1 pp.2) hmem
    rw [show N = n i i' + (N - n i i') from (Nat.add_sub_cancel' hle).symm, pow_add, ← mul_assoc,
      hn i hi i' hi' hne, zero_mul]
  refine ⟨∑ i ∈ t, e i ^ (N + 1) * a i, ∑ i ∈ t, e i ^ (N + 1) * b i, fun i hi => ?_⟩
  -- the terms with `i' ≠ i` lie in `P i`
  have hrest : ∀ c : ι → A, ∑ i' ∈ t.erase i, e i' ^ (N + 1) * c i' ∈ (P i).asIdeal := by
    intro c
    refine Ideal.sum_mem _ fun i' hi' => ?_
    have hi'' := Finset.mem_erase.mp hi'
    exact (P i).asIdeal.mul_mem_right _
      ((P i).asIdeal.pow_mem_of_mem (he_mem i' hi''.2 i hi hi''.1.symm) _ (Nat.succ_pos N))
  have hsplit : ∀ c : ι → A, ∑ i' ∈ t, e i' ^ (N + 1) * c i' =
      (∑ i' ∈ t.erase i, e i' ^ (N + 1) * c i') + e i ^ (N + 1) * c i :=
    fun c => (Finset.sum_erase_add t _ hi).symm
  have hnot : ∀ c : ι → A, c i ∉ (P i).asIdeal →
      ∑ i' ∈ t, e i' ^ (N + 1) * c i' ∉ (P i).asIdeal := by
    intro c hc hmem
    rw [hsplit] at hmem
    have h1 : e i ^ (N + 1) * c i ∈ (P i).asIdeal := by
      have := (P i).asIdeal.sub_mem hmem (hrest c)
      simpa using this
    rcases (P i).isPrime.mem_or_mem h1 with h | h
    · exact he_notMem i hi ((P i).isPrime.mem_of_pow_mem _ h)
    · exact hc h
  refine ⟨hnot a (ha i hi), hnot b (hb i hi), ∏ i' ∈ t.erase i, y i i', ?_, ?_⟩
  · intro hmem
    obtain ⟨i', hi', hcon⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (P i).isPrime)).mp hmem
    have hi'' := Finset.mem_erase.mp hi'
    exact hy i hi i' hi''.2 hi''.1 hcon
  · have hkill : ∀ i' ∈ t.erase i, (∏ i'' ∈ t.erase i, y i i'') * e i' ^ (N + 1) = 0 := by
      intro i' hi'
      have hi'' := Finset.mem_erase.mp hi'
      rw [← Finset.mul_prod_erase (t.erase i) (y i) hi', mul_right_comm, pow_succ, ← mul_assoc,
        hN i hi i' hi''.2 hi''.1, zero_mul, zero_mul]
    have hred : ∀ c : ι → A,
        (∏ i'' ∈ t.erase i, y i i'') * ∑ i' ∈ t, e i' ^ (N + 1) * c i' =
          (∏ i'' ∈ t.erase i, y i i'') * (e i ^ (N + 1) * c i) := by
      intro c
      rw [hsplit, mul_add, Finset.mul_sum, Finset.sum_eq_zero, zero_add]
      intro i' hi'
      rw [← mul_assoc, hkill i' hi', zero_mul]
    calc (∏ i'' ∈ t.erase i, y i i'') * ((∑ i' ∈ t, e i' ^ (N + 1) * a i') * b i)
        = ((∏ i'' ∈ t.erase i, y i i'') * ∑ i' ∈ t, e i' ^ (N + 1) * a i') * b i := by ring
      _ = ((∏ i'' ∈ t.erase i, y i i'') * (e i ^ (N + 1) * a i)) * b i := by rw [hred]
      _ = ((∏ i'' ∈ t.erase i, y i i'') * (e i ^ (N + 1) * b i)) * a i := by ring
      _ = ((∏ i'' ∈ t.erase i, y i i'') * ∑ i' ∈ t, e i' ^ (N + 1) * b i') * a i := by rw [hred]
      _ = (∏ i'' ∈ t.erase i, y i i'') * ((∑ i' ∈ t, e i' ^ (N + 1) * b i') * a i) := by ring

/-- `Ann_S(m/1) = S⁻¹ Ann_A(m)` for a localization `S` of `A` at `M`. -/
theorem IsLocalization.colon_bot_singleton_map {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (m : A) :
    (⊥ : Submodule S S).colon {algebraMap A S m} =
      ((⊥ : Submodule A A).colon {m}).map (algebraMap A S) := by
  apply le_antisymm
  · intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hr
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective M r
    have h1 : algebraMap A S (a * m) = 0 := by
      rw [map_mul, ← IsLocalization.mk'_spec' S a t, mul_assoc, hr, mul_zero]
    rw [IsLocalization.map_eq_zero_iff M] at h1
    obtain ⟨u, hu⟩ := h1
    rw [IsLocalization.mem_map_algebraMap_iff M]
    refine ⟨⟨⟨(u : A) * a, ?_⟩, u * t⟩, ?_⟩
    · rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul, mul_assoc]
      exact hu
    · simp only [Submonoid.coe_mul, map_mul]
      rw [mul_left_comm, IsLocalization.mk'_spec]
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul, ← map_mul, hr,
      map_zero]

/-- If `q = rad(Ann_A m)` (so `q ∈ Ass_A(A)`), then the maximal ideal of `A_q` is an associated prime
of `A_q`. -/
theorem IsLocalization.AtPrime.maximalIdeal_mem_associatedPrimes_of_eq_radical {A S : Type*}
    [CommRing A] [CommRing S] [Algebra A S] [IsLocalRing S] (q : Ideal A) [q.IsPrime]
    [IsLocalization.AtPrime S q] (m : A) (hq : q = ((⊥ : Submodule A A).colon {m}).radical) :
    IsLocalRing.maximalIdeal S ∈ associatedPrimes S S := by
  refine ⟨(IsLocalRing.maximalIdeal.isMaximal S).isPrime, algebraMap A S m, ?_⟩
  rw [IsLocalization.colon_bot_singleton_map q.primeCompl m, ← IsLocalization.map_radical q.primeCompl,
    ← hq, IsLocalization.AtPrime.map_eq_maximalIdeal q S]

/-- If `q` is a minimal prime of `A`, then the maximal ideal of `A_q` is an associated prime of `A_q`
(it is the radical of `Ann(1) = 0`). -/
theorem IsLocalization.AtPrime.maximalIdeal_mem_associatedPrimes_of_mem_minimalPrimes {A S : Type*}
    [CommRing A] [CommRing S] [Algebra A S] [IsLocalRing S] (q : Ideal A) [q.IsPrime]
    [IsLocalization.AtPrime S q] (hq : q ∈ (⊥ : Ideal A).minimalPrimes) :
    IsLocalRing.maximalIdeal S ∈ associatedPrimes S S := by
  refine ⟨(IsLocalRing.maximalIdeal.isMaximal S).isPrime, 1, ?_⟩
  have h1 : (⊥ : Submodule S S).colon {1} = ⊥ := by
    ext r
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_one]
  have h2 : ((⊥ : Ideal A).map (algebraMap A S)).radical = IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes S q ⊥ hq,
      IsLocalization.AtPrime.map_eq_maximalIdeal q S]
  rw [Ideal.map_bot] at h2
  rw [h1]
  exact h2.symm

end
