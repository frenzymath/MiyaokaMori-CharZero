import MiyaokaMori.Prelude

/-! # Finiteness of the height-one primes containing an element

In a Noetherian domain `A`, for `a ≠ 0` there are only finitely many height-one primes containing `a`
(they are all minimal primes of `(a)`).

References: first sentence of the proof of Stacks 0EAW ("Thus the sum is finite …
V(ab) = {𝔪, 𝔮_1, …, 𝔮_r}"); Stacks 00FR/0ALV (a Noetherian ring has finitely many minimal primes).
-/

set_option autoImplicit false

universe u

/-- Proof: let `q` have height `1` with `a ∈ q`. If a prime `p` satisfies `span {a} ≤ p ≤ q`, then `p ≠ ⊥`
(`a ≠ 0`), and `p < q` would give the chain `⊥ < p < q` and `Ideal.height q ≥ 2` (strict monotonicity of
`Ideal.height` / `Order.height`: `Ideal.bot_prime` has height `0 < height p < height q`), a contradiction;
hence `p = q` and `q ∈ (Ideal.span {a}).minimalPrimes`. Finiteness:
`Ideal.finite_minimalPrimes_of_isNoetherianRing`, pulled back along the injection `fun q => q.asIdeal`
(`Set.Finite.preimage` + `PrimeSpectrum.ext`). Edge case: if `a` is a unit the set is empty. -/
theorem PrimeSpectrum.finite_height_one_mem {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {a : A} (ha : a ≠ 0) :
    {q : PrimeSpectrum A | q.asIdeal.height = 1 ∧ a ∈ q.asIdeal}.Finite := by
  -- Every such `q` is a minimal prime over `(a)`; minimal primes are finite in a noetherian ring.
  have hfin : ((Ideal.span {a}).minimalPrimes).Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing A _
  refine Set.Finite.subset (hfin.preimage (f := fun q : PrimeSpectrum A => q.asIdeal)
    (fun q _ q' _ h => PrimeSpectrum.ext h)) ?_
  rintro q ⟨hq1, hqa⟩
  show q.asIdeal ∈ (Ideal.span {a}).minimalPrimes
  have hle : Ideal.span {a} ≤ q.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hqa
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hle
  have hpprime : p.IsPrime := hp.isPrime
  -- `p ≠ ⊥` since `a ∈ p` and `a ≠ 0`, hence `height p ≥ 1 = height q`, so `p = q`.
  have hpbot : p ≠ ⊥ := by
    intro h
    have : a ∈ p := hp.1.2 (Ideal.mem_span_singleton_self a)
    rw [h, Ideal.mem_bot] at this
    exact ha this
  have h1 : 1 ≤ p.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hpbot
  have hpq' : p = q.asIdeal := Ideal.eq_of_le_of_height_le p hpq (hq1 ▸ h1)
  exact hpq' ▸ hp
