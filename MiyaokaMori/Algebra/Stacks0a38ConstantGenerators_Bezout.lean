import MiyaokaMori.Prelude

/-! # Finite gcd bookkeeping for Stacks 0A38

Three elementary facts about `Finset.gcd` on `ℕ`:
* `Finset.exists_int_sum_mul_eq_gcd`: Bézout, `gcd_{j ∈ J} n_j = ∑_{j ∈ J} a_j n_j` for some `a_j ∈ ℤ`
  (induction on `J` from `Int.gcd_eq_gcd_ab`);
* `Finset.gcd_biUnion_eq_gcd_gcd`: `gcd_{j ∈ ⋃_{J ∈ S} J} n_j = gcd_{J ∈ S} gcd_{j ∈ J} n_j`
  (induction on `S` from `Finset.gcd_union`);
* `Finset.gcd_pos_of_forall_pos`: the gcd of a nonempty family of positive integers is positive.

Source: Stacks 0A38, proof, paragraph 2 ("for every subset add the gcd of the corresponding integers"). -/

set_option autoImplicit false

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- **Bézout for `Finset.gcd`**: `gcd_{j ∈ J} n_j` is an integer linear combination of the `n_j`, `j ∈ J`. -/
theorem exists_int_sum_mul_eq_gcd (J : Finset ι) (n : ι → ℕ) :
    ∃ a : ι → ℤ, ∑ j ∈ J, a j * (n j : ℤ) = ((J.gcd n : ℕ) : ℤ) := by
  induction J using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i J hi ih =>
    obtain ⟨a, ha⟩ := ih
    rw [Finset.gcd_insert, gcd_eq_nat_gcd, ← Int.gcd_natCast_natCast, Int.gcd_eq_gcd_ab]
    set A := Int.gcdA (n i : ℤ) ((J.gcd n : ℕ) : ℤ)
    set B := Int.gcdB (n i : ℤ) ((J.gcd n : ℕ) : ℤ)
    refine ⟨fun j => if j = i then A else a j * B, ?_⟩
    have this : ∀ j ∈ J, (if j = i then A else a j * B) * (n j : ℤ) = a j * (n j : ℤ) * B := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [if_neg hji]
      ring
    rw [Finset.sum_insert hi]
    dsimp only
    rw [if_pos rfl, Finset.sum_congr rfl this, ← Finset.sum_mul, ha]
    ring

/-- the gcd over a finite union of finite sets is the gcd of the gcds -/
theorem gcd_biUnion_eq_gcd_gcd {κ : Type*} [DecidableEq κ] (S : Finset κ) (T : κ → Finset ι) (n : ι → ℕ) :
    (S.biUnion T).gcd n = S.gcd (fun k => (T k).gcd n) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih => rw [Finset.biUnion_insert, Finset.gcd_union, Finset.gcd_insert, ih]

omit [DecidableEq ι] in
/-- the gcd of a nonempty family of positive integers is positive -/
theorem gcd_pos_of_forall_pos {J : Finset ι} (hJ : J.Nonempty) {n : ι → ℕ} (hn : ∀ j ∈ J, 0 < n j) :
    0 < J.gcd n := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Finset.gcd_eq_zero_iff] at h
  obtain ⟨j, hj⟩ := hJ
  exact (hn j hj).ne' (h j hj)

end Finset
