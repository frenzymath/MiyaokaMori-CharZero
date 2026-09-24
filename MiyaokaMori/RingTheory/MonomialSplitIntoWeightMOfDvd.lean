import MiyaokaMori.Prelude
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Splitting a monomial of weight `l · m` into monomials of weight `m`

Let `σ` be a finite set of variables with weights `w : σ → ℕ` taking values in `[1, k]`, and let
`m > 0` be divisible by **every** `q ∈ [1, k]`. If a monomial `e` has weight `∑ᵢ wᵢ eᵢ = l · m`
(`l ≥ 1`), then `e = f₀ + ⋯ + f_{l-1}` with every `fⱼ` of weight exactly `m`.

This generalizes `exists_split_of_weight_eq_mul` from `m = |σ| · lcm(1..k)` to an arbitrary `m`
divisible by `1, …, k`; the splitting of the weighted algebra and of the tautological class use it
for arbitrary such `m` (and for `m · k!`), so the special `m` of the paper does not suffice.

## Proof

The paper only treats `m = s_k w_k` and its multiples (pigeonhole, §2 of the paper); the general
case is proved here by a self-contained elementary argument.

Equivalent multiset form (`MonomialSplitOfDvd.core`): `S` is a multiset of variables
(`e.toMultiset`), with weight sum `wsum S = ∑_{i ∈ S} w i`. One proves by induction on `k` the
stronger statement with a slack `E`:

> weights in `[1,k]`, every `q ≤ k` divides `m`, `E + Hb k ≤ m`, `2m ≤ wsum S + E` ⟹ there is
> `A ≤ S` with `wsum A = m`,

where `Hb 0 = 0`, `Hb (k+1) = max (k²) ((k+1)(k-1) + Hb k)` (values `0,0,1,4,12,27,51,86,134,197,277,…`).
Induction step `K = k+1`: let `n` be the number of elements of weight exactly `K`, and `S'` the
remaining elements (weights in `[1,k]`).
* (i) `nK ≥ m`: take `m/K` elements of weight `K`.
* (ii) `nK < m` and `n ≥ K-1`: Lemma Z′ (`exists_le_dvd_of_bound`) gives `A' ≤ S'` with
  `K ∣ wsum A'` and `m - nK ≤ wsum A' ≤ m - nK + K(K-1) ≤ m`; add `(m - wsum A')/K ≤ n` elements of
  weight `K`.
* (iii) `nK < m` and `n ≤ K-2`: discard the elements of weight `K` (loss `≤ K(K-2)`) and apply the
  induction hypothesis to `S'` with slack `E' = E + K(K-2)`.

Lemma Z′: weights in `[1,K-1]` and `wsum S ≥ u + (K-1)²` ⟹ there is `A ≤ S` with `K ∣ wsum A` and
`u ≤ wsum A ≤ u + K(K-1)`. Strong induction on `card S`: among any `K` elements, two of the `K+1`
prefix sums agree mod `K` (`Fintype.exists_ne_map_eq_of_card_lt`), giving a nonempty block `B` of
weight sum divisible by `K` (`card B ≤ K`, `wsum B ≤ K(K-1)`, `exists_block`); if `wsum B ≥ u` take
`B`, otherwise recurse on `S - B` and `u - wsum B`.

Finally `Hb k ≤ m` (`Hb_le`): for `k ≤ 3` directly (`Hb 3 = 4 ≤ 6 ≤ m`); for `k ≥ 4`,
`k(k-1) ∣ m` (coprime factors) and `(k-2) ∣ m`, `gcd(k(k-1), k-2) ≤ 2`, hence
`k(k-1)(k-2) = gcd · lcm ≤ 2m`, while `2 Hb k ≤ k(k-1)(k-2)` (induction).
Main theorem: `l = 1` is trivial; for `l ≥ 2` the weight is `≥ 2m`, `exists_sub_weight` extracts a
sub-monomial of weight `m`, and one inducts on `l`.

Remark: the hypothesis "all of `1..k` divide `m`" cannot be weakened to "the weights that occur
divide `m`": for `m = 30` the multiset `{15, 10, 10, 6, 6, 6, 6, 1}` (sum `60`) has no sub-multiset
of sum `30`. Full divisibility is used in (ii) (`K ∣ m` at every level) and in `Hb_le`
(`k, k-1, k-2 ∣ m`). The hypothesis `[Fintype σ]` is not used in the proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace MonomialSplitOfDvd

variable {σ : Type u} (w : σ → ℕ)

/-- Weighted sum of a multiset of variables. -/
def wsum (S : Multiset σ) : ℕ := (S.map w).sum

@[simp] theorem wsum_zero : wsum w (0 : Multiset σ) = 0 := by simp [wsum]

theorem wsum_add (A B : Multiset σ) : wsum w (A + B) = wsum w A + wsum w B := by
  simp [wsum, Multiset.map_add, Multiset.sum_add]

theorem wsum_sub [DecidableEq σ] {A S : Multiset σ} (h : A ≤ S) :
    wsum w (S - A) = wsum w S - wsum w A := by
  have := wsum_add w (S - A) A
  rw [tsub_add_cancel_of_le h] at this
  omega

theorem wsum_le_card_mul (B : Multiset σ) (c : ℕ) (h : ∀ i ∈ B, w i ≤ c) :
    wsum w B ≤ Multiset.card B * c := by
  have := Multiset.sum_le_card_nsmul (B.map w) c (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact h i hi)
  simpa [wsum, Multiset.card_map, smul_eq_mul] using this

theorem wsum_eq_card_mul (B : Multiset σ) (c : ℕ) (h : ∀ i ∈ B, w i = c) :
    wsum w B = Multiset.card B * c := by
  unfold wsum
  rw [Multiset.map_congr rfl (fun i hi => h i hi), Multiset.map_const', Multiset.sum_replicate,
    smul_eq_mul]

theorem wsum_coe (l : List σ) : wsum w (l : Multiset σ) = (l.map w).sum := by
  simp [wsum]

/-- Any multiset of card `≤ c` can be cut down to a sub-multiset of exactly card `c`. -/
theorem exists_le_card_eq (T : Multiset σ) (c : ℕ) (hc : c ≤ Multiset.card T) :
    ∃ B ≤ T, Multiset.card B = c := by
  have hne : Multiset.powersetCard c T ≠ 0 := by
    rw [← Multiset.card_pos, Multiset.card_powersetCard]
    exact Nat.choose_pos hc
  obtain ⟨B, hB⟩ := Multiset.exists_mem_of_ne_zero hne
  exact ⟨B, (Multiset.mem_powersetCard.mp hB).1, (Multiset.mem_powersetCard.mp hB).2⟩

/-- Zero-sum block (Davenport constant of `ℤ/K`): any `K` elements contain a nonempty
sub-multiset whose weighted sum is divisible by `K`. Pigeonhole on the `K+1` prefix sums mod `K`. -/
theorem exists_block (K : ℕ) (hK : 1 ≤ K) (S : Multiset σ) (hS : K ≤ Multiset.card S) :
    ∃ B ≤ S, B ≠ 0 ∧ Multiset.card B ≤ K ∧ K ∣ wsum w B := by
  induction S using Quotient.inductionOn with
  | _ l =>
  simp only [Multiset.quot_mk_to_coe, Multiset.coe_card] at hS ⊢
  -- auxiliary: two prefix sums of `l` at positions `a < a + d ≤ K` with the same residue
  have aux : ∀ a d : ℕ, a + d ≤ K → 0 < d →
      ((l.take a).map w).sum % K = ((l.take (a + d)).map w).sum % K →
      ∃ B ≤ (l : Multiset σ), B ≠ 0 ∧ Multiset.card B ≤ K ∧ K ∣ wsum w B := by
    intro a d had hd hmod
    refine ⟨(((l.drop a).take d : List σ) : Multiset σ), ?_, ?_, ?_, ?_⟩
    · exact Multiset.coe_le.mpr
        (((List.take_sublist _ _).trans (List.drop_sublist _ _)).subperm)
    · rw [Ne, Multiset.coe_eq_zero, ← List.length_eq_zero_iff, List.length_take,
        List.length_drop]
      omega
    · rw [Multiset.coe_card, List.length_take]
      omega
    · rw [wsum_coe]
      have h1 : l.take (a + d) = l.take a ++ (l.drop a).take d := List.take_add
      rw [h1, List.map_append, List.sum_append] at hmod
      have := (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mp hmod
      simpa using this
  -- pigeonhole
  let P : Fin (K + 1) → Fin K := fun i => ⟨((l.take i).map w).sum % K, Nat.mod_lt _ hK⟩
  obtain ⟨i, j, hij, hP⟩ := Fintype.exists_ne_map_eq_of_card_lt P (by simp)
  have hP' : ((l.take i).map w).sum % K = ((l.take j).map w).sum % K := by
    simpa [P] using congrArg Fin.val hP
  rcases lt_or_gt_of_ne hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) = i + d := ⟨j - i, by have := h; omega⟩
    exact aux i d (by have := j.isLt; omega) (by have := (Fin.lt_def.mp h); omega)
      (by rw [← hd]; exact hP')
  · obtain ⟨d, hd⟩ : ∃ d, (i : ℕ) = j + d := ⟨i - j, by have := h; omega⟩
    exact aux j d (by have := i.isLt; omega) (by have := (Fin.lt_def.mp h); omega)
      (by rw [← hd]; exact hP'.symm)


/-- Lemma Z′: if the weights of `S` lie in `[1, K-1]` and `wsum S ≥ u + (K-1)²`, then some
sub-multiset has weighted sum divisible by `K` and lying in `[u, u + K(K-1)]`.
Proof: strong induction on `card S`; peel a zero-sum block `B` (`exists_block`, `wsum B ≤ K(K-1)`);
if `wsum B ≥ u` take `B`, else recurse on `S - B` with `u - wsum B`. -/
theorem exists_le_dvd_of_bound [DecidableEq σ] (K : ℕ) (hK : 1 ≤ K) :
    ∀ (n : ℕ) (S : Multiset σ), Multiset.card S = n →
      (∀ i ∈ S, 1 ≤ w i ∧ w i ≤ K - 1) → ∀ u : ℕ, u + (K - 1) * (K - 1) ≤ wsum w S →
      ∃ A ≤ S, K ∣ wsum w A ∧ u ≤ wsum w A ∧ wsum w A ≤ u + K * (K - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS u hu
  by_cases hcard : Multiset.card S ≤ K - 1
  · have hle : wsum w S ≤ (K - 1) * (K - 1) := by
      have := wsum_le_card_mul w S (K - 1) (fun i hi => (hS i hi).2)
      have h2 : Multiset.card S * (K - 1) ≤ (K - 1) * (K - 1) :=
        Nat.mul_le_mul_right _ hcard
      omega
    have hu0 : u = 0 := by omega
    subst hu0
    exact ⟨0, Multiset.zero_le _, by simp, le_rfl, by simp⟩
  · obtain ⟨B, hBS, hB0, hBcard, hBdvd⟩ := exists_block w K hK S (by omega)
    have hBle : wsum w B ≤ K * (K - 1) := by
      have := wsum_le_card_mul w B (K - 1)
        (fun i hi => (hS i (Multiset.mem_of_le hBS hi)).2)
      exact this.trans (Nat.mul_le_mul_right _ hBcard)
    by_cases hub : u ≤ wsum w B
    · exact ⟨B, hBS, hBdvd, hub, by omega⟩
    · have hBpos : 0 < Multiset.card B := Multiset.card_pos.mpr hB0
      have hcardlt : Multiset.card (S - B) < n := by
        rw [Multiset.card_sub hBS]; omega
      have hsub := wsum_sub w hBS
      obtain ⟨A', hA'S, hA'dvd, hA'lo, hA'hi⟩ := ih _ hcardlt (S - B) rfl
        (fun i hi => hS i (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi))
        (u - wsum w B) (by omega)
      refine ⟨A' + B, add_le_of_le_tsub_right_of_le hBS hA'S, ?_, ?_, ?_⟩
      · rw [wsum_add]; exact dvd_add hA'dvd hBdvd
      · rw [wsum_add]; omega
      · rw [wsum_add]; omega

/-- The loss bound `Hb K`: the weighted sum must satisfy `m ≥ E + Hb K` for the core induction.
`Hb (k+1) = max (k²) ((k+1)(k-1) + Hb k)`. Values: 0, 0, 1, 4, 12, 27, 51, 86, 134, 197, 277, … -/
def Hb : ℕ → ℕ
  | 0 => 0
  | k + 1 => max (k * k) ((k + 1) * (k - 1) + Hb k)

/-- Core combinatorial statement, by induction on `k` (the largest allowed weight).
Let `K = k+1`, `n` = number of elements of weight `K`.
(i) `n K ≥ m`: take `m/K` of them.
(ii) `n K < m`, `n ≥ K-1`: remove all weight-`K` elements; Lemma Z′ on the rest with `u = m - nK`
    gives `A'` with `K ∣ wsum A'`, `u ≤ wsum A' ≤ u + K(K-1) ≤ m`; fill up with `(m - wsum A')/K ≤ n`
    elements of weight `K`.
(iii) `n K < m`, `n < K-1`: discard the weight-`K` elements (loss `≤ K(K-2)`) and use the
    induction hypothesis with `E' = E + K(K-2)`. -/
theorem core [DecidableEq σ] :
    ∀ (k E m : ℕ) (S : Multiset σ), (∀ i ∈ S, 1 ≤ w i ∧ w i ≤ k) →
      (∀ q, 1 ≤ q → q ≤ k → q ∣ m) → E + Hb k ≤ m → 2 * m ≤ wsum w S + E →
      ∃ A ≤ S, wsum w A = m
  | 0, E, m, S, hS, _hdiv, hH, hsum => by
    have hS0 : S = 0 := Multiset.eq_zero_of_forall_notMem (fun i hi => by
      have := hS i hi; omega)
    subst hS0
    simp only [wsum_zero, Hb] at hsum hH
    exact ⟨0, le_rfl, by simp; omega⟩
  | k + 1, E, m, S, hS, hdiv, hH, hsum => by
    set K := k + 1 with hKdef
    have hK : 1 ≤ K := by omega
    have hKm : K ∣ m := hdiv K hK le_rfl
    have hHb : Hb K = max (k * k) ((k + 1) * (k - 1) + Hb k) := rfl
    set T := S.filter (fun i => w i = K) with hTdef
    set S' := S.filter (fun i => ¬ w i = K) with hS'def
    have hST : T + S' = S := Multiset.filter_add_not _ S
    have hTS : T ≤ S := Multiset.filter_le _ S
    have hS'S : S' ≤ S := Multiset.filter_le _ S
    set n := Multiset.card T with hndef
    have hTw : ∀ i ∈ T, w i = K := fun i hi => (Multiset.mem_filter.mp hi).2
    have hwT : wsum w T = n * K := wsum_eq_card_mul w T K hTw
    have hS'w : ∀ i ∈ S', 1 ≤ w i ∧ w i ≤ k := by
      intro i hi
      have h1 := hS i (Multiset.mem_of_le hS'S hi)
      have h2 := (Multiset.mem_filter.mp hi).2
      omega
    have hsplit : wsum w S = n * K + wsum w S' := by
      rw [← hST, wsum_add, hwT]
    by_cases hi : m ≤ n * K
    · -- case (i)
      have hc : m / K ≤ n := Nat.div_le_of_le_mul (by rw [mul_comm]; exact hi)
      obtain ⟨B, hBT, hBcard⟩ := exists_le_card_eq T (m / K) hc
      refine ⟨B, hBT.trans hTS, ?_⟩
      rw [wsum_eq_card_mul w B K (fun i hi => hTw i (Multiset.mem_of_le hBT hi)), hBcard]
      exact Nat.div_mul_cancel hKm
    · by_cases hii : k ≤ n
      · -- case (ii)
        have hkk : k * k ≤ Hb K := by rw [hHb]; exact le_max_left _ _
        obtain ⟨A', hA'S', hA'dvd, hA'lo, hA'hi⟩ :=
          exists_le_dvd_of_bound w K hK _ S' rfl (by simpa [hKdef] using hS'w) (m - n * K)
            (by
              have : K - 1 = k := by omega
              rw [this]; omega)
        have hA'm : wsum w A' ≤ m := by
          have : K - 1 = k := by omega
          rw [this] at hA'hi
          have : K * k ≤ n * K := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hii
          omega
        have hdvd : K ∣ m - wsum w A' := Nat.dvd_sub hKm hA'dvd
        set j := (m - wsum w A') / K with hjdef
        have hjK : j * K = m - wsum w A' := Nat.div_mul_cancel hdvd
        have hjn : j ≤ n := by
          have : j * K ≤ n * K := by omega
          exact Nat.le_of_mul_le_mul_right this (by omega)
        obtain ⟨B, hBT, hBcard⟩ := exists_le_card_eq T j hjn
        refine ⟨A' + B, ?_, ?_⟩
        · rw [← hST, add_comm T S']
          exact add_le_add hA'S' hBT
        · rw [wsum_add, wsum_eq_card_mul w B K (fun i hi => hTw i (Multiset.mem_of_le hBT hi)),
            hBcard, hjK]
          omega
      · -- case (iii)
        have hloss : (k + 1) * (k - 1) + Hb k ≤ Hb K := by rw [hHb]; exact le_max_right _ _
        have hnk : n * K ≤ (k + 1) * (k - 1) := by
          rw [hKdef, mul_comm]
          exact Nat.mul_le_mul_left _ (by omega)
        obtain ⟨A, hAS', hA⟩ := core k (E + (k + 1) * (k - 1)) m S' hS'w
          (fun q hq1 hqk => hdiv q hq1 (by omega)) (by omega) (by omega)
        exact ⟨A, hAS'.trans hS'S, hA⟩


/-- `2 · Hb k ≤ k(k-1)(k-2)` for `k ≥ 4` (induction; base `Hb 4 = 12`). -/
theorem two_mul_Hb_le (j : ℕ) : 2 * Hb (j + 4) ≤ (j + 4) * (j + 3) * (j + 2) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h1 : Hb (j + 1 + 4) = max ((j + 4) * (j + 4)) ((j + 5) * (j + 3) + Hb (j + 4)) := by
      show max ((j + 4) * (j + 4)) ((j + 4 + 1) * (j + 4 - 1) + Hb (j + 4)) = _
      congr 2
    rw [h1]
    rcases le_total ((j + 4) * (j + 4)) ((j + 5) * (j + 3) + Hb (j + 4)) with hle | hle
    · rw [max_eq_right hle]; nlinarith
    · rw [max_eq_left hle]; nlinarith

/-- If every `q ∈ [1,k]` divides `m > 0`, then `Hb k ≤ m`.
For `k ≤ 3` directly (`Hb 3 = 4 ≤ 6 ≤ m`); for `k ≥ 4`, `k(k-1) ∣ m` (coprime) and `(k-2) ∣ m`,
`gcd (k(k-1)) (k-2) ≤ 2`, so `k(k-1)(k-2) = gcd · lcm ≤ 2 m`, and `2 Hb k ≤ k(k-1)(k-2)`. -/
theorem Hb_le (k m : ℕ) (hm : 0 < m) (hdiv : ∀ q, 1 ≤ q → q ≤ k → q ∣ m) : Hb k ≤ m := by
  match k with
  | 0 => simp [Hb]
  | 1 => simp [Hb]
  | 2 => show max 1 (2 * 0 + max 0 (1 * 0 + 0)) ≤ m; omega
  | 3 =>
    have h6 : 6 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3)
      (hdiv 2 (by norm_num) (by norm_num)) (hdiv 3 (by norm_num) (by norm_num))
    have : 6 ≤ m := Nat.le_of_dvd hm h6
    show max 4 (3 * 1 + max 1 (2 * 0 + max 0 (1 * 0 + 0))) ≤ m
    omega
  | j + 4 =>
    have ha : (j + 4) * (j + 3) ∣ m :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by
          rw [Nat.coprime_comm, show j + 4 = (j + 3) + 1 from rfl]
          exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _))
        (hdiv _ (by omega) le_rfl) (hdiv _ (by omega) (by omega))
    have hb : j + 2 ∣ m := hdiv _ (by omega) (by omega)
    have hlcm : Nat.lcm ((j + 4) * (j + 3)) (j + 2) ∣ m := Nat.lcm_dvd ha hb
    have hlcm_le : Nat.lcm ((j + 4) * (j + 3)) (j + 2) ≤ m := Nat.le_of_dvd hm hlcm
    have hgcd : Nat.gcd ((j + 4) * (j + 3)) (j + 2) ≤ 2 := by
      have hcop : Nat.Coprime (j + 4) (j + 3) := by
        rw [Nat.coprime_comm, show j + 4 = (j + 3) + 1 from rfl]
        exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul _ hcop]
      have h1 : Nat.gcd (j + 2) (j + 3) = 1 := by
        rw [show j + 3 = (j + 2) + 1 from rfl]
        exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      have h2 : Nat.gcd (j + 2) (j + 4) ∣ 2 := by
        rw [show j + 4 = (j + 2) + 2 from rfl, Nat.gcd_self_add_right]
        exact Nat.gcd_dvd_right _ _
      rw [h1, mul_one]
      exact Nat.le_of_dvd (by norm_num) h2
    have hprod : (j + 4) * (j + 3) * (j + 2) ≤ 2 * m := by
      calc (j + 4) * (j + 3) * (j + 2)
          = Nat.gcd ((j + 4) * (j + 3)) (j + 2) * Nat.lcm ((j + 4) * (j + 3)) (j + 2) :=
            (Nat.gcd_mul_lcm _ _).symm
        _ ≤ 2 * m := Nat.mul_le_mul hgcd hlcm_le
    have := two_mul_Hb_le j
    omega

/-- `wsum` of `Finsupp.toMultiset` is `Finsupp.weight`. -/
theorem wsum_toMultiset (e : σ →₀ ℕ) : wsum w (Finsupp.toMultiset e) = Finsupp.weight w e := by
  induction e using Finsupp.induction with
  | zero => simp [wsum]
  | single_add a n f _ _ ih =>
    rw [Finsupp.toMultiset_add, wsum_add, ih, map_add, Finsupp.toMultiset_single,
      Finsupp.weight_single]
    simp [wsum, Multiset.map_nsmul, Multiset.sum_nsmul, smul_eq_mul]

/-- Extraction of one sub-monomial of weight exactly `m` (the `l = 2` case of the target). -/
theorem exists_sub_weight {k : ℕ} (hw : ∀ i, 1 ≤ w i ∧ w i ≤ k) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q, 1 ≤ q → q ≤ k → q ∣ m) (e : σ →₀ ℕ) (h : 2 * m ≤ Finsupp.weight w e) :
    ∃ f₀ e' : σ →₀ ℕ, f₀ + e' = e ∧ Finsupp.weight w f₀ = m := by
  classical
  obtain ⟨A, hA, hAw⟩ := core w k 0 m (Finsupp.toMultiset e) (fun i _ => hw i) hdiv
    (by simpa using Hb_le k m hm hdiv) (by rw [wsum_toMultiset]; omega)
  refine ⟨Multiset.toFinsupp A, Multiset.toFinsupp (Finsupp.toMultiset e - A), ?_, ?_⟩
  · rw [← Multiset.toFinsupp_add, add_tsub_cancel_of_le hA, Finsupp.toMultiset_toFinsupp]
  · rw [← wsum_toMultiset, Multiset.toFinsupp_toMultiset, hAw]

end MonomialSplitOfDvd

/-- A monomial of weight `l · m` is a product of `l` monomials of weight `m` (when `m` is divisible by
all of `1..k`). For the proof route see the module docstring. -/
theorem exists_split_of_weight_eq_mul_of_dvd {σ : Type u} [Fintype σ] {k : ℕ} (w : σ → ℕ)
    (hw : ∀ i, w i ∈ Finset.Icc 1 k) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 k, q ∣ m) (e : σ →₀ ℕ) (l : ℕ) (hl : 1 ≤ l)
    (h : Finsupp.weight w e = l * m) :
    ∃ f : Fin l → (σ →₀ ℕ), (∀ j, Finsupp.weight w (f j) = m) ∧ ∑ j, f j = e := by
  have hw' : ∀ i, 1 ≤ w i ∧ w i ≤ k := fun i => Finset.mem_Icc.mp (hw i)
  have hdiv' : ∀ q, 1 ≤ q → q ≤ k → q ∣ m := fun q h1 h2 => hdiv q (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  induction l generalizing e with
  | zero => omega
  | succ l ih =>
    rcases Nat.eq_zero_or_pos l with rfl | hlpos
    · exact ⟨fun _ => e, fun _ => by simpa using h, by simp⟩
    · obtain ⟨f₀, e', hsum, hf₀⟩ := MonomialSplitOfDvd.exists_sub_weight w hw' m hm hdiv' e
        (by rw [h]; nlinarith)
      have he' : Finsupp.weight w e' = l * m := by
        have := congrArg (Finsupp.weight w) hsum
        rw [map_add, hf₀, h] at this
        nlinarith
      obtain ⟨g, hg, hgsum⟩ := ih e' hlpos he'
      refine ⟨Fin.cons f₀ g, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ ?_ j
        · simpa using hf₀
        · intro i; simpa using hg i
      · rw [Fin.sum_cons, hgsum, hsum]

end
