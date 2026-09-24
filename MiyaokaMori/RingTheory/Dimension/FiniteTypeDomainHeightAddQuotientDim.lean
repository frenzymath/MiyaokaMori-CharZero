import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainSaturatedChain

/-! # The dimension formula `dim A/𝔭 + height 𝔭 = dim A` for finite type domains

Let `k` be a field, `A` a finite type `k`-algebra which is a domain, and `𝔭` a prime ideal of `A`.
Then `dim A/𝔭 + height 𝔭 = dim A` (the dimension formula for finite type `k`-domains).

Proof:
1. `A` is Noetherian, so `height 𝔭 = n` is finite; choose a chain of primes `P_0 ⊂ … ⊂ P_n = 𝔭` of
   length exactly `n` ending at `𝔭` (Mathlib `Ideal.exists_ltSeries_length_eq_height`).
2. The length equals the height of the last term, so `height P_i = i` for every `i`
   (`Order.height_eq_index_of_length_eq_height_last`). Hence `P_0` has height `0` and is minimal
   (`Order.height_eq_zero`), and there is no prime strictly between consecutive terms: if
   `P_i < c < P_{i+1}` then `height P_{i+1} ≥ height c + 1 ≥ height P_i + 2 = i + 2`
   (`Order.height_add_one_le`), contradicting `height P_{i+1} = i + 1`.
3. By the saturated-chain version (`FiniteTypeDomainSaturatedChain`): `dim A/P_n + n = dim A`, i.e.
   `dim A/𝔭 + height 𝔭 = dim A`.

Reference: a consequence of Stacks 00OS; Hartshorne, *Algebraic Geometry*, I Thm 1.8A(b).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

theorem ringKrullDim_quotient_add_height_eq {k : Type u} [Field k] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (p : Ideal A) [hp : p.IsPrime] :
    ringKrullDim (A ⧸ p) + (p.height : WithBot ℕ∞) = ringKrullDim A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨l, hlast, hlen⟩ := p.exists_ltSeries_length_eq_height
  have hlen' : (l.length : ℕ∞) = Order.height l.last := by
    rw [hlen, ← PrimeSpectrum.height_eq_orderHeight, hlast]
  have hidx := fun i => Order.height_eq_index_of_length_eq_height_last hlen' i
  have hhead : IsMin l.head := by
    have h0 : Order.height l.head = 0 := (hidx 0).trans (by simp)
    exact Order.height_eq_zero.mp h0
  have hcov : ∀ i : Fin l.length, l.toFun i.castSucc ⋖ l.toFun i.succ := by
    intro i
    refine ⟨l.step i, fun c h1 h2 => ?_⟩
    have e1 : Order.height (l.toFun i.castSucc) = (i : ℕ) := by simpa using hidx i.castSucc
    have e2 : Order.height (l.toFun i.succ) = ((i : ℕ) + 1 : ℕ) := by simpa using hidx i.succ
    have k1 := Order.height_add_one_le h1
    have k2 := Order.height_add_one_le h2
    rw [e1] at k1
    rw [e2] at k2
    have : ((i : ℕ) : ℕ∞) + 1 + 1 ≤ ((i : ℕ) + 1 : ℕ) := le_trans (by gcongr) k2
    have h' : (i : ℕ) + 1 + 1 ≤ (i : ℕ) + 1 := by exact_mod_cast this
    omega
  have key := ringKrullDim_quotient_last_add_length_of_covBy_chain (k := k) A l hhead hcov
  rw [hlast] at key
  rw [← hlen]
  exact key

end
