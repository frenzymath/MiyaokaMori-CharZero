import MiyaokaMori.RingTheory.Length.PeriodicComplexLength

/-! # Periodic complexes built from powers of a nilpotent endomorphism

Let `R` be a ring, `M` an `R`-module, `t : M → M` linear, `n > 0`, `tⁿ = 0`, and suppose `Ker t / Im tⁿ⁻¹`
has finite length. Then for `0 ≤ i ≤ n` the `(2,1)`-periodic complex `(M, tⁱ, tⁿ⁻ⁱ)` has finite-length
cohomology and `e_R(M, tⁱ, tⁿ⁻ⁱ) = 0`.

Proof. Write `K_i = Ker tⁱ`, `I_j = Im tʲ`, `A(i, j) = l(K_i/(K_i ∩ I_j)) ∈ ℕ∞` (relative length,
`PeriodicComplexLength`).
1. `K_i ∩ I_j = tʲ(K_{i+j})`.
2. (The `ℕ∞` form of the four-term exact sequences.) For all `i`, `k`, `j` there is `s` with
   `A(i+k, j) = A(k, j) + s` and `A(i, j+k) = s + A(i, k)`: take the chain `X ≤ X + K_k ≤ K_{i+k}`
   (`X = K_{i+k} ∩ I_j`); the first step equals `l(K_k/(K_k ∩ I_j)) = A(k, j)` by the second isomorphism
   theorem; the second step, pushed forward by `t^k` (`Ker t^k ∩ K_{i+k} = K_k`), equals
   `s := l((K_i ∩ I_k)/(K_i ∩ I_{j+k}))` (using step 1); then the chain `K_i ∩ I_{j+k} ≤ K_i ∩ I_k ≤ K_i`
   gives the second equation. (The two four-term exact sequences of the original are the special cases
   `k = 1` and `(i,k,j) = (1,i,1)`.)
3. `b_i := A(i, 1)` and `c_i := A(1, i)` agree: by induction on `i`, step 2 with `(1, i, 1)` gives
   `b_{i+1} = b_i + s`, `c_{i+1} = s + c_i`; `b_0 = c_0 = 0`.
4. `a_i := A(i, n − i)`. Step 2 with `(i, 1, n−1−i)`: `a_{i+1} = c_{n−1−i} + s`, `a_i = s + b_i`.
   `c_j ≤ c_{n−1} < ∞` (`j ≤ n − 1`, `c_{n−1} = l(Ker t/Im tⁿ⁻¹)`), `a_0 = 0`, so by induction `a_i` is
   finite and in `ℤ`, `a_{i+1} − a_i = c_{n−1−i} − c_i`.
5. By 4, `a_i − a_{n−i}` is independent of `i` (the difference of consecutive terms is
   `(c_{n−1−i} − c_i) + (c_i − c_{n−1−i}) = 0`), hence equals `a_0 − a_n = 0`
   (`a_n = l(K_n/K_n ∩ I_0) = 0`). And `l H⁰(tⁱ, tⁿ⁻ⁱ) = a_i`, `l H¹ = a_{n−i}`.

Reference: Stacks 0EAB (chow-lemma-powers-period-length-zero).
-/

set_option autoImplicit false

open Submodule

namespace PeriodicComplex

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

theorem relLength_eq_zero_of_le {A B : Submodule R M} (h : B ≤ A) : relLength A B = 0 := by
  unfold relLength
  rw [Submodule.submoduleOf_eq_top.mpr h]
  exact Module.length_eq_zero

theorem relLength_anti_left {A A' : Submodule R M} (h : A ≤ A') (B : Submodule R M) :
    relLength A' B ≤ relLength A B := by
  rw [← relLength_congr_inf A, ← relLength_congr_inf A',
    relLength_add (inf_le_inf_right B h) inf_le_right]
  exact le_add_self

namespace Powers

variable (t : Module.End R M)

/-- `A(i, j) = l(K_i/(K_i ∩ I_j))`. -/
noncomputable def A (i j : ℕ) : ℕ∞ := relLength (LinearMap.range (t ^ j)) (LinearMap.ker (t ^ i))

theorem ker_mono {i j : ℕ} (h : i ≤ j) : LinearMap.ker (t ^ i) ≤ LinearMap.ker (t ^ j) := by
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [LinearMap.mem_ker] at hx ⊢
  rw [add_comm, pow_add, Module.End.mul_apply, hx, map_zero]

theorem ker_inf_range (i j m : ℕ) (hm : m = i + j) :
    LinearMap.ker (t ^ i) ⊓ LinearMap.range (t ^ j) = (LinearMap.ker (t ^ m)).map (t ^ j) := by
  subst hm
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, by rw [pow_add, Module.End.mul_apply, hx], rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by rw [← Module.End.mul_apply, ← pow_add, hy], y, rfl⟩

/-- The `ℕ∞` form of the four-term exact sequence. -/
theorem exists_A (i k j : ℕ) :
    ∃ s : ℕ∞, A t (i + k) j = A t k j + s ∧ A t i (j + k) = s + A t i k := by
  refine ⟨relLength (LinearMap.ker (t ^ i) ⊓ LinearMap.range (t ^ (j + k)))
    (LinearMap.ker (t ^ i) ⊓ LinearMap.range (t ^ k)), ?_, ?_⟩
  · set X := LinearMap.range (t ^ j) ⊓ LinearMap.ker (t ^ (i + k)) with hX
    have hk : LinearMap.ker (t ^ k) ≤ LinearMap.ker (t ^ (i + k)) := ker_mono t (Nat.le_add_left k i)
    unfold A
    rw [← relLength_congr_inf, ← hX,
      relLength_add (le_sup_left : X ≤ X ⊔ LinearMap.ker (t ^ k)) (sup_le inf_le_right hk)]
    congr 1
    · rw [relLength_sup_left, ← relLength_congr_inf, hX, inf_assoc, inf_eq_right.mpr hk,
        relLength_congr_inf]
    · rw [← relLength_map (t ^ k) (sup_le inf_le_right hk) (inf_le_of_left_le le_sup_right),
        Submodule.map_sup, ← ker_inf_range t i k (i + k) rfl]
      congr 1
      have e1 : (LinearMap.ker (t ^ k)).map (t ^ k) = ⊥ :=
        eq_bot_iff.mpr (by
          rintro _ ⟨y, hy, rfl⟩
          exact (Submodule.mem_bot R).mpr (LinearMap.mem_ker.mp hy))
      rw [e1, sup_bot_eq, inf_comm (LinearMap.range (t ^ j)), ker_inf_range t (i + k) j (i + k + j) rfl,
        ← Submodule.map_comp, ker_inf_range t i (j + k) (i + k + j) (by ring)]
      congr 1
      rw [← Module.End.mul_eq_comp, ← pow_add, add_comm]
  · unfold A
    rw [← relLength_congr_inf (LinearMap.range (t ^ (j + k))),
      ← relLength_congr_inf (LinearMap.range (t ^ k)),
      inf_comm (LinearMap.range (t ^ (j + k))) (LinearMap.ker (t ^ i)),
      inf_comm (LinearMap.range (t ^ k)) (LinearMap.ker (t ^ i))]
    refine relLength_add (inf_le_inf_left _ ?_) inf_le_left
    rintro _ ⟨y, rfl⟩
    exact ⟨(t ^ j) y, by rw [← Module.End.mul_apply, ← pow_add, add_comm]⟩

theorem A_zero_left (j : ℕ) : A t 0 j = 0 := by
  unfold A
  refine relLength_eq_zero_of_le ?_
  rw [pow_zero]
  intro x hx
  have : x = 0 := hx
  rw [this]; exact Submodule.zero_mem _

theorem A_zero_right (i : ℕ) : A t i 0 = 0 := by
  unfold A
  refine relLength_eq_zero_of_le ?_
  rw [pow_zero]
  intro x _
  exact ⟨x, rfl⟩

/-- `b_i = c_i`. -/
theorem A_one_comm (i : ℕ) : A t i 1 = A t 1 i := by
  induction i with
  | zero => rw [A_zero_left, A_zero_right]
  | succ i ih =>
    obtain ⟨s, h1, h2⟩ := exists_A t 1 i 1
    rw [add_comm 1 i] at h1 h2
    rw [h1, h2, ih, add_comm]

theorem A_one_le (n j : ℕ) (hj : j ≤ n) : A t 1 j ≤ A t 1 n := by
  unfold A
  refine relLength_anti_left ?_ _
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rintro _ ⟨y, rfl⟩
  exact ⟨(t ^ k) y, by rw [← Module.End.mul_apply, ← pow_add]⟩

variable {t}

/-- Step 4: `a_i` is finite, and `a_{i+1} + c_i = a_i + c_{n−1−i}` (`i < n`; here `c` is written as `A 1 ·`). -/
theorem step (n : ℕ) (hfin : A t 1 (n - 1) ≠ ⊤) (i : ℕ) (hi : i < n) (hai : A t i (n - i) ≠ ⊤) :
    A t (i + 1) (n - (i + 1)) ≠ ⊤ ∧
      ((A t (i + 1) (n - (i + 1))).toNat : ℤ) - (A t i (n - i)).toNat =
        ((A t 1 (n - 1 - i)).toNat : ℤ) - (A t 1 i).toNat := by
  obtain ⟨s, h1, h2⟩ := exists_A t i 1 (n - (i + 1))
  have e : n - (i + 1) + 1 = n - i := by omega
  rw [e, A_one_comm] at h2
  have hc : A t 1 (n - (i + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (A_one_le t (n - 1) _ (by omega))
  have hs : s ≠ ⊤ := fun hs => hai (by rw [h2, hs, top_add])
  have hb : A t 1 i ≠ ⊤ := fun hb => hai (by rw [h2, hb, add_top])
  refine ⟨by rw [h1]; exact WithTop.add_ne_top.mpr ⟨hc, hs⟩, ?_⟩
  have e' : n - 1 - i = n - (i + 1) := by omega
  rw [h1, h2, e', ENat.toNat_add hc hs, ENat.toNat_add hs hb]
  push_cast
  ring

theorem finite_and_diff (n : ℕ) (hfin : A t 1 (n - 1) ≠ ⊤) (i : ℕ) (hi : i ≤ n) :
    A t i (n - i) ≠ ⊤ := by
  induction i with
  | zero => rw [A_zero_left]; exact ENat.zero_ne_top
  | succ i ih => exact (step n hfin i (by omega) (ih (by omega))).1

theorem symm_aux (n : ℕ) (hfin : A t 1 (n - 1) ≠ ⊤) (i : ℕ) (hi : i ≤ n) :
    ((A t i (n - i)).toNat : ℤ) - (A t (n - i) (n - (n - i))).toNat =
      ((A t 0 (n - 0)).toNat : ℤ) - (A t (n - 0) (n - (n - 0))).toNat := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 := (step n hfin i (by omega) (finite_and_diff n hfin i (by omega))).2
    have h2 := (step n hfin (n - (i + 1)) (by omega)
      (finite_and_diff n hfin (n - (i + 1)) (by omega))).2
    have e1 : n - (i + 1) + 1 = n - i := by omega
    have e2 : n - 1 - (n - (i + 1)) = i := by omega
    have e3 : n - 1 - i = n - (i + 1) := by omega
    rw [e1, e2] at h2
    rw [e3] at h1
    have := ih (by omega)
    omega

end Powers

open Powers in
/-- Stacks 0EAB: if `Ker t/Im tⁿ⁻¹` has finite length then `e(M, tⁱ, tⁿ⁻ⁱ) = 0`. The hypothesis `tⁿ = 0` of the
original is only used to make `(tⁱ, tⁿ⁻ⁱ)` a complex and is not needed in the proof (`H φ ψ` is defined for
arbitrary `φ`, `ψ` as `Ker φ/(Im ψ ∩ Ker φ)`), so it is not assumed. -/
theorem herbrand_pow_eq_zero (t : Module.End R M) (n : ℕ) (hn : 0 < n)
    (hfin : Module.length R (H t (t ^ (n - 1))) ≠ ⊤) (i : ℕ) (hi : i ≤ n) :
    FiniteCohomology (t ^ i) (t ^ (n - i)) ∧ herbrand (t ^ i) (t ^ (n - i)) = 0 := by
  have hfin' : A t 1 (n - 1) ≠ ⊤ := by
    unfold A; rw [pow_one]; exact hfin
  have h0 : Module.length R (H (t ^ i) (t ^ (n - i))) = A t i (n - i) := rfl
  have h1 : Module.length R (H (t ^ (n - i)) (t ^ i)) = A t (n - i) (n - (n - i)) := by
    have : n - (n - i) = i := by omega
    rw [this]; rfl
  have hA0 : A t 0 (n - 0) = 0 := A_zero_left t _
  have hAn : A t (n - 0) (n - (n - 0)) = 0 := by
    have : n - (n - 0) = 0 := by omega
    rw [this]; exact A_zero_right t _
  have key := symm_aux n hfin' i hi
  rw [hA0, hAn] at key
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h0]; exact finite_and_diff n hfin' i hi
  · rw [h1]
    have := finite_and_diff n hfin' (n - i) (by omega)
    exact this
  · unfold herbrand
    rw [h0, h1]
    simpa using key

end PeriodicComplex
