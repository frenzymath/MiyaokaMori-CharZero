import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainHeightOneQuotient

/-! # Saturated chains of primes in a finite type domain

Let `k` be a field, `S` a finite type `k`-algebra which is a domain, and `P_0 ⊂ P_1 ⊂ … ⊂ P_l` a
chain of primes of `S` with `P_0` minimal (i.e. `P_0 = 0`) and no prime strictly between consecutive
terms (`P_i ⋖ P_{i+1}`). Then `dim S/P_i + i = dim S` for every `i ≤ l`; in particular
`dim S/P_l + l = dim S`.

Proof:
1. Induction on `i`. `i = 0`: `P_0` is a minimal element of `Spec S`; `S` is a domain so `(0)` is
   prime and `(0) ≤ P_0`, hence `P_0 = (0)` and `S/(0) ≅ S` (`RingEquiv.quotientBot`).
2. `i → i+1`: `A = S/P_i` is a finite type `k`-domain and `Q' = P_{i+1}/P_i` is a prime of `A`.
   `P_i ⋖ P_{i+1}` gives `height Q' = 1`: `Q' ≠ 0` (`P_i ≠ P_{i+1}`); if `q ⊂ Q'` is a prime of
   `A`, its preimage `c` satisfies `P_i ≤ c < P_{i+1}`, so `c = P_i` by `⋖`, i.e. `q = 0`; hence
   all primes below `Q'` have height `< 1` (`Ideal.height_le_iff`).
3. By `FiniteTypeDomainHeightOneQuotient`: `dim A/Q' + 1 = dim A`, and `A/Q' ≅ S/P_{i+1}`
   (`DoubleQuot.quotQuotEquivQuotOfLE`). Combined with the induction hypothesis
   `dim S/P_i + i = dim S` this gives `dim S/P_{i+1} + (i+1) = dim S`.

Reference: the induction step of "all maximal chains have the same length" in Stacks 00OS.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

/-- For consecutive primes `P ⋖ Q`, the image of `Q` in `S ⧸ P` has height `1`. -/
private theorem height_map_quotient_eq_one_of_covBy {S : Type u} [CommRing S]
    {P Q : PrimeSpectrum S} (h : P ⋖ Q) :
    (Q.asIdeal.map (Ideal.Quotient.mk P.asIdeal)).height = 1 := by
  have hPQ : P.asIdeal ≤ Q.asIdeal := h.1.le
  have hprime : (Q.asIdeal.map (Ideal.Quotient.mk P.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  refine le_antisymm ?_ ?_
  · rw [← Nat.cast_one, Ideal.height_le_iff]
    intro q hq hlt
    let c : PrimeSpectrum S := ⟨q.comap (Ideal.Quotient.mk P.asIdeal), inferInstance⟩
    have hPc : P ≤ c := by
      change P.asIdeal ≤ q.comap (Ideal.Quotient.mk P.asIdeal)
      intro x hx
      simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    have hmc : c.asIdeal.map (Ideal.Quotient.mk P.asIdeal) = q :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
    have hcQ : c < Q := by
      refine lt_of_le_of_ne ?_ ?_
      · change q.comap (Ideal.Quotient.mk P.asIdeal) ≤ Q.asIdeal
        intro x hx
        have hx' : Ideal.Quotient.mk P.asIdeal x ∈ Q.asIdeal.map (Ideal.Quotient.mk P.asIdeal) :=
          hlt.le hx
        rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx'
        obtain ⟨y, hy, hxy⟩ := hx'
        have : x - y ∈ P.asIdeal := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hxy, sub_self]
        have := Q.asIdeal.add_mem (hPQ this) hy
        simpa using this
      · rintro rfl
        exact hlt.ne hmc.symm
    have hcP : c = P := by
      by_contra hne
      exact h.2 (lt_of_le_of_ne hPc (Ne.symm hne)) hcQ
    have hq0 : q = ⊥ := by
      rw [← hmc, hcP, Ideal.map_quotient_self]
    rw [hq0]
    have : Nontrivial (S ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
    simp [Ideal.height_bot]
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot,
      Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact fun hle => h.1.not_ge hle

theorem ringKrullDim_quotient_add_index_of_covBy_chain {k : Type u} [Field k] (S : Type u)
    [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
    (l : LTSeries (PrimeSpectrum S)) (hhead : IsMin l.head)
    (hcov : ∀ i : Fin l.length, l.toFun i.castSucc ⋖ l.toFun i.succ) :
    ∀ i : ℕ, ∀ hi : i ≤ l.length,
      ringKrullDim (S ⧸ (l.toFun ⟨i, Nat.lt_succ_of_le hi⟩).asIdeal) + (i : WithBot ℕ∞) =
        ringKrullDim S := by
  intro i
  induction i with
  | zero =>
    intro _
    have h0 : (l.toFun ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩).asIdeal = ⊥ := by
      have hle : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) ≤ l.head := bot_le (a := l.head.asIdeal)
      exact le_bot_iff.mp (hhead hle)
    rw [h0, Nat.cast_zero, add_zero]
    exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S)
  | succ i ih =>
    intro hi
    have hi' : i < l.length := hi
    have hc := hcov ⟨i, hi'⟩
    set P := l.toFun (Fin.castSucc ⟨i, hi'⟩) with hPdef
    set Q := l.toFun (Fin.succ ⟨i, hi'⟩) with hQdef
    have hPQ : P.asIdeal ≤ Q.asIdeal := hc.1.le
    have hprime : (Q.asIdeal.map (Ideal.Quotient.mk P.asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hPQ
    have : Algebra.FiniteType k (S ⧸ P.asIdeal) := Algebra.FiniteType.quotient k P.asIdeal
    have hK := ringKrullDim_quotient_add_one_of_height_eq_one (k := k) (S ⧸ P.asIdeal)
      (Q.asIdeal.map (Ideal.Quotient.mk P.asIdeal)) (height_map_quotient_eq_one_of_covBy hc)
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)] at hK
    have ih' := ih hi'.le
    change ringKrullDim (S ⧸ P.asIdeal) + (i : WithBot ℕ∞) = ringKrullDim S at ih'
    change ringKrullDim (S ⧸ Q.asIdeal) + ((i + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim S
    rw [← ih', ← hK, Nat.cast_add, Nat.cast_one]
    abel

theorem ringKrullDim_quotient_last_add_length_of_covBy_chain {k : Type u} [Field k] (S : Type u)
    [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
    (l : LTSeries (PrimeSpectrum S)) (hhead : IsMin l.head)
    (hcov : ∀ i : Fin l.length, l.toFun i.castSucc ⋖ l.toFun i.succ) :
    ringKrullDim (S ⧸ l.last.asIdeal) + (l.length : WithBot ℕ∞) = ringKrullDim S :=
  ringKrullDim_quotient_add_index_of_covBy_chain (k := k) S l hhead hcov l.length le_rfl

end
