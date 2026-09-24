import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.Paper.S2WeightedJets.Ygg.MonomialDivisibleByWeightPower

/-! # Splitting a monomial of weight `ℓm` into `ℓ` monomials of weight `m`

A monomial of weight `ℓ · m`, `m = s · w_k`, is a product of `ℓ` monomials of weight `m`:
repeatedly remove factors of weight `w_k` and group them in blocks of `s`
(proof of Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem exists_split_of_weight_eq_mul {s k : ℕ} (w : Fin s → ℕ)
    (hw : ∀ i, w i ∈ Finset.Icc 1 k) (e : Fin s →₀ ℕ) (l : ℕ) (hl : 1 ≤ l)
    (h : Finsupp.weight w e = l * (s * jetWeight k)) :
    ∃ f : Fin l → (Fin s →₀ ℕ),
      (∀ j, Finsupp.weight w (f j) = s * jetWeight k) ∧ ∑ j, f j = e := by
  classical
  let q : ℕ := jetWeight k
  let m : ℕ := s * q
  have hq : 0 < q := by
    dsimp [q, jetWeight]
    rw [Nat.pos_iff_ne_zero, Finset.lcm_ne_zero_iff]
    intro i hi
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hi).1
  have hsum_snoc {n : ℕ}
      (f : Fin n → (Fin s →₀ ℕ)) (a : Fin s →₀ ℕ) :
      ∑ i, Fin.snoc f a i = (∑ i, f i) + a := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

  have peel : ∀ (n : ℕ) (x : Fin s →₀ ℕ),
      (s + n) * q ≤ Finsupp.weight w x →
      ∃ (r : Fin s →₀ ℕ) (f : Fin n → (Fin s →₀ ℕ)),
        x = r + ∑ j, f j ∧
          Finsupp.weight w r + n * q = Finsupp.weight w x ∧
          ∀ j, Finsupp.weight w (f j) = q := by
    intro n
    induction n with
    | zero =>
        intro x hx
        refine ⟨x, (fun i => Fin.elim0 i), ?_, ?_, ?_⟩
        · simp
        · simp
        · intro i
          exact Fin.elim0 i
    | succ n ih =>
        intro x hx
        have hlt : s * q < Finsupp.weight w x := by
          have hsn : s * q < (s + (n + 1)) * q := by
            exact Nat.mul_lt_mul_of_pos_right (by omega) hq
          exact lt_of_lt_of_le hsn hx
        obtain ⟨i, hi⟩ := exists_pow_dvd_of_weight_gt w hw x hlt
        let a : ℕ := q / w i
        have hdiv : w i ∣ q := by
          change w i ∣ (Finset.Icc 1 k).lcm id
          exact Finset.dvd_lcm (s := Finset.Icc 1 k) (f := id) (b := w i) (hw i)
        have ha : a * w i = q := by
          dsimp [a]
          exact Nat.div_mul_cancel hdiv
        have hia : a ≤ x i := by exact hi
        have hsingle : Finsupp.single i a ≤ x := Finsupp.single_le_iff.mpr hia
        let y : Fin s →₀ ℕ := x - Finsupp.single i a
        have hweight_step' : Finsupp.weight w (x - Finsupp.single i a) + a * w i =
            Finsupp.weight w x := by
          have he := add_tsub_cancel_of_le hsingle
          rw [← he, map_add, Finsupp.weight_single]
          simp [smul_eq_mul, add_comm]
        have hweight_step : Finsupp.weight w y + q = Finsupp.weight w x := by
          calc
            Finsupp.weight w y + q =
                Finsupp.weight w (x - Finsupp.single i a) + a * w i := by
                  simp [y, ha]
            _ = Finsupp.weight w x := hweight_step'
        have hybound : (s + n) * q ≤ Finsupp.weight w y := by
          have hrew : (s + n) * q + q = (s + (n + 1)) * q := by
            ring
          have haux : (s + n) * q + q ≤ Finsupp.weight w x := by
            calc
              (s + n) * q + q = (s + (n + 1)) * q := hrew
              _ ≤ Finsupp.weight w x := hx
          rw [← hweight_step] at haux
          exact Nat.le_of_add_le_add_right haux
        obtain ⟨r, f, hy, hwr, hf⟩ := ih y hybound
        refine ⟨r, Fin.snoc f (Finsupp.single i a), ?_, ?_, ?_⟩
        have hxy : x = y + Finsupp.single i a := by
          calc
            x = Finsupp.single i a + y := (add_tsub_cancel_of_le hsingle).symm
            _ = y + Finsupp.single i a := add_comm _ _
        · calc
            x = y + Finsupp.single i a := hxy
            _ = (r + ∑ j, f j) + Finsupp.single i a := by rw [hy]
            _ = r + ((∑ j, f j) + Finsupp.single i a) := by simp [add_assoc]
            _ = r + ∑ j, Fin.snoc f (Finsupp.single i a) j := by
              exact congrArg (fun z : Fin s →₀ ℕ => r + z)
                (hsum_snoc f (Finsupp.single i a)).symm
        ·
          have hwr' : Finsupp.weight w r + (n + 1) * q =
              Finsupp.weight w y + q := by
            calc
              Finsupp.weight w r + (n + 1) * q =
                  (Finsupp.weight w r + n * q) + q := by
                    rw [Nat.add_mul]
                    omega
              _ = Finsupp.weight w y + q := by rw [hwr]
          exact hwr'.trans hweight_step
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · rw [Fin.snoc_last, Finsupp.weight_single]
            simpa [a, smul_eq_mul] using ha
          · simpa only [Fin.snoc_castSucc] using hf j

  have split : ∀ (n : ℕ) (x : Fin s →₀ ℕ), 1 ≤ n →
      Finsupp.weight w x = n * (s * jetWeight k) →
      ∃ f : Fin n → (Fin s →₀ ℕ),
        (∀ j, Finsupp.weight w (f j) = s * jetWeight k) ∧ ∑ j, f j = x := by
    intro n
    induction n with
    | zero => intro x hn; omega
    | succ n ih =>
        intro x hn hx
        by_cases hn0 : n = 0
        · subst n
          refine ⟨fun _ => x, ?_, ?_⟩
          · intro j
            have hj : j = 0 := Fin.eq_zero j
            subst j
            simpa using hx
          · simp
        · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
          have hbound : (s + s) * q ≤ Finsupp.weight w x := by
            have hsle : 2 * (s * q) ≤ (n + 1) * (s * q) :=
              Nat.mul_le_mul_right (s * q) (by omega)
            calc
              (s + s) * q = 2 * (s * q) := by ring
              _ ≤ (n + 1) * (s * q) := hsle
              _ = Finsupp.weight w x := hx.symm
          obtain ⟨r, g, hsplit, hwr, hg⟩ := peel s x hbound
          have hr : Finsupp.weight w r = n * (s * jetWeight k) := by
            have hrr' : Finsupp.weight w r + s * q = (n + 1) * (s * q) :=
              hwr.trans (by simpa [q] using hx)
            have hrr'' : Finsupp.weight w r + s * q = n * (s * q) + s * q := by
              simpa [Nat.add_mul] using hrr'
            have hrq : Finsupp.weight w r = n * (s * q) := Nat.add_right_cancel hrr''
            simpa [q] using hrq
          obtain ⟨f, hf, hsum⟩ := ih r hnpos hr
          let d : Fin s →₀ ℕ := ∑ j, g j
          have hd : Finsupp.weight w d = s * jetWeight k := by
            dsimp [d]
            rw [map_sum]
            simp_rw [hg]
            simp [q]
          refine ⟨Fin.snoc f d, ?_, ?_⟩
          · intro j
            refine Fin.lastCases ?_ (fun j => ?_) j
            · simpa only [Fin.snoc_last] using hd
            · simpa only [Fin.snoc_castSucc] using hf j
          · calc
              ∑ j, Fin.snoc f d j = (∑ j, f j) + d := by
                exact hsum_snoc f d
              _ = r + d := by rw [hsum]
              _ = x := hsplit.symm

  exact split l e hl h

end
