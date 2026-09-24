import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nq

/-! # Stacks 00NP: regular local rings are domains

Stacks 00NP: a regular local ring is a domain.

Reference: Stacks 00NP (first sentence of the proof of 0AG0).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Prime avoidance: choose `x ∈ m ∖ (m² ∪ ⋃ minimal primes)`.**

Reference: first step of the proof of Matsumura, *Commutative Ring Theory*, Thm 14.3 / Bruns–Herzog Prop 2.2.3;
prime avoidance = Stacks 00DS.

Statement: `R` a Noetherian local ring whose maximal ideal `m` is not a minimal prime of `R` (i.e. `dim R ≥ 1`);
then there is `x ∈ m`, `x ∉ m²`, lying in no minimal prime.

Proof:
1. `minimalPrimes R` is finite (`minimalPrimes.finite_of_isNoetherianRing R`); take its `Finset`, say `P_1..P_k`.
2. Apply `Ideal.subset_union_prime` (index set `Option (minimalPrimes R)`, or `Finset (Ideal R)` plus one extra
   point for `m²`; the lemma allows the ideals at two indices `a b` to be non-prime, so put `m ^ 2` at `a`): if
   `(m : Set R) ⊆ m² ∪ ⋃ P_i`, then `m ≤ m²` or `m ≤ P_i` for some `i`.
3. `m ≤ P_i` is impossible: `P_i` is prime so `P_i ≤ m` (`IsLocalRing.le_maximalIdeal`), hence
   `m = P_i ∈ minimalPrimes R`, contradicting the hypothesis.
4. `m ≤ m²` is impossible: `m ≤ m • m` (`pow_two`, `Ideal.smul_eq_mul`), and Nakayama
   (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m m (IsNoetherian.noetherian _) h (IsLocalRing.maximalIdeal_le_jacobson _)`)
   gives `m = ⊥`; but `⊥ = m` is prime and obviously minimal (by the definition of `minimalPrimes`: minimal among
   primes `p` with `⊥ ≤ p`), so `m ∈ minimalPrimes R`, a contradiction.
5. Hence `(m : Set R) ⊄ m² ∪ ⋃ P_i`; extract a witness `x` (`Set.not_subset`).

Edge cases: a field (`m = ⊥`): `⊥` is a minimal prime, the hypothesis fails. Likewise for Artinian local rings.
`R` need not be reduced (reducedness is not used). -/
theorem IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : IsLocalRing.maximalIdeal R ∉ minimalPrimes R) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, x ∉ IsLocalRing.maximalIdeal R ^ 2 ∧
      ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  by_contra hcon
  push Not at hcon
  have hsub : ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ i ∈ ((insert (IsLocalRing.maximalIdeal R ^ 2) hfin.toFinset : Finset (Ideal R)) :
        Set (Ideal R)), ((id i : Ideal R) : Set R) := by
    intro x hx
    by_cases hx2 : x ∈ IsLocalRing.maximalIdeal R ^ 2
    · exact Set.mem_biUnion (by simp) hx2
    · obtain ⟨p, hp, hxp⟩ := hcon x hx hx2
      exact Set.mem_biUnion (by simp [hp]) hxp
  obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (f := id) (IsLocalRing.maximalIdeal R ^ 2)
    (IsLocalRing.maximalIdeal R ^ 2) (fun i hi h1 _ => by
      have : i ∈ minimalPrimes R := by
        rcases Finset.mem_insert.mp hi with h' | h'
        · exact absurd h' h1
        · exact hfin.mem_toFinset.mp h'
      exact this.1.1)).mp hsub
  rcases Finset.mem_insert.mp hp with rfl | hp'
  · -- `m ≤ m²` ⇒ `m = ⊥` ⇒ `m` is a minimal prime
    have hle : IsLocalRing.maximalIdeal R ≤
        IsLocalRing.maximalIdeal R • IsLocalRing.maximalIdeal R := by
      rw [smul_eq_mul, ← pow_two]; exact hmp
    have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) hle
        (IsLocalRing.maximalIdeal_le_jacobson _)
    refine h ⟨⟨(IsLocalRing.maximalIdeal.isMaximal R).isPrime, bot_le⟩, fun y _ _ => ?_⟩
    rw [hbot]; exact bot_le
  · have hpmin : p ∈ minimalPrimes R := hfin.mem_toFinset.mp hp'
    have hpm : p ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hpmin.1.1.ne_top
    exact h (le_antisymm hpm hmp ▸ hpmin)

/-- The last step of the proof of 00NP (Matsumura Thm 14.3 / Bruns–Herzog 2.2.3): in a Noetherian local ring, if
`(x)` is prime, `x ∈ m` and `x` lies in no minimal prime, then `R` is a domain. Take a minimal prime `p ⊆ (x)`:
`a = r x ∈ p` and `x ∉ p` ⇒ `r ∈ p`, so `p ≤ m • p`, and Nakayama ⇒ `p = ⊥`. -/
theorem IsLocalRing.isDomain_of_span_singleton_isPrime {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hprime : (Ideal.span {x}).IsPrime) (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) : IsDomain R := by
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Ideal.span {x}) bot_le
  have hpprime : p.IsPrime := hp.1.1
  have hle : p ≤ IsLocalRing.maximalIdeal R • p := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp (hpx ha)
    have hr : r ∈ p := (hpprime.mem_or_mem ha).resolve_right (hmin p hp)
    rw [mul_comm]
    exact Submodule.smul_mem_smul hx hr
  have hbot : p = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) p
      (IsNoetherian.noetherian p) hle (IsLocalRing.maximalIdeal_le_jacobson _)
  have : (⊥ : Ideal R).IsPrime := hbot ▸ hpprime
  exact IsDomain.of_bot_isPrime R

/-- A regular local ring whose maximal ideal is a minimal prime is a field (`dim = 0` ⇒ `spanFinrank m = 0` ⇒
`m = ⊥`). -/
theorem IsRegularLocalRing.isDomain_of_maximalIdeal_mem_minimalPrimes {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (h : IsLocalRing.maximalIdeal R ∈ minimalPrimes R) : IsDomain R := by
  have h0 : ringKrullDim R = 0 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, Ideal.height_eq_zero_iff.mpr h]
    rfl
  have h1 : (IsLocalRing.maximalIdeal R).spanFinrank = 0 := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [h0] at this
    exact_mod_cast this
  have h2 : IsLocalRing.maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h1
  exact (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h2).isDomain

/-- The inductive form of 00NP: strong induction on `n = spanFinrank m` (quantified over all rings `R`; the
quotient `R/(x)` lives in the same universe as `R`). -/
theorem IsRegularLocalRing.isDomain_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = n → IsDomain R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ hn
    by_cases hmin : IsLocalRing.maximalIdeal R ∈ minimalPrimes R
    · exact IsRegularLocalRing.isDomain_of_maximalIdeal_mem_minimalPrimes hmin
    · obtain ⟨x, hx, hx2, hxmin⟩ :=
        IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hmin
      have hreg : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
        IsRegularLocalRing.quotient_span_singleton hx hx2
      have hlt : (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank < n := by
        have := IsLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le hx hx2
        omega
      have hdom : IsDomain (R ⧸ Ideal.span {x}) := ih _ hlt (R ⧸ Ideal.span {x}) rfl
      have hprime : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime (I := Ideal.span {x})).mp hdom
      exact IsLocalRing.isDomain_of_span_singleton_isPrime hx hprime hxmin

/-- **Stacks 00NP: a regular local ring is a domain.** (`IsDomain` is a `Prop`-valued class; this instance carries
no data.)

Mathlib (`Mathlib/RingTheory/RegularLocalRing/`) has the definition of `IsRegularLocalRing`,
`iff_finrank_cotangentSpace`, PID ⇒ regular, `IsRegularRing`, and `Polynomial.lean`, but neither
`IsRegularLocalRing → IsDomain` nor Auslander–Buchsbaum.

Proof route (not the original proof of Stacks 00NP, which uses 00NO and would be circular with our proof of 00NO;
this is the prime-avoidance induction of Matsumura, *Commutative Ring Theory*, Thm 14.3 / Bruns–Herzog Prop
2.2.3, see `isDomain_of_spanFinrank_eq` above):
1. `d = 0`: `spanFinrank (maximalIdeal R) = 0` ⇒ `maximalIdeal R = ⊥` (`Submodule.spanFinrank_eq_zero_iff` and
   the like) ⇒ `R` is a field (`IsLocalRing.isField_iff_maximalIdeal_eq`) ⇒ a domain.
2. `d > 0`: `R` is Noetherian local with finitely many minimal primes (`minimalPrimes.finite_of_isNoetherianRing`).
   By Nakayama `m ≠ m²`, and by prime avoidance (`Ideal.subset_union_prime`) take
   `x ∈ m \ (m² ∪ ⋃_{p minimal} p)`.
   * `R/(x)` is again a regular local ring with `dim R/(x) = d - 1`: `x ∉ m²` makes `m/(x)` generated by `d-1`
     elements (`Ideal.spanFinrank` drops by `1` in the quotient), while `dim R/(x) ≥ d - 1` (Krull's principal
     ideal theorem, Mathlib `Ideal.KrullsHeightTheorem`); then `of_spanFinrank_maximalIdeal_le`.
   * The induction hypothesis ⇒ `R/(x)` is a domain ⇒ `(x)` is prime.
   * Take a minimal prime `p ⊆ (x)`. For `a ∈ p`, write `a = r·x`; `x ∉ p` (by choice) and `p` prime ⇒ `r ∈ p`.
     Hence `p = x·p ⊆ m·p`, and Nakayama ⇒ `p = ⊥`. So `⊥` is prime and `R` is a domain.

The two ingredients not in Mathlib are `Stacks00nq.quotient_span_singleton` (a regular local ring modulo an element
of `m \ m²` is regular of dimension one less) and the prime-avoidance lemma of this file.

The instance has priority `low`: it is declared late, and at default priority instance search would try it first,
so that even "a field `k` is a domain" would be resolved through `IsRegularLocalRing.isDomain k` (a field is a PID,
hence a regular local ring), changing instance paths throughout the import closure. It is a `Prop` instance and
does not affect any decidability. -/
instance (priority := low) IsRegularLocalRing.isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain_of_spanFinrank_eq _ R rfl

end
