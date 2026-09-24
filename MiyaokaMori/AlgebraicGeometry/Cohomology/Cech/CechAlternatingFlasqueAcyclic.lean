import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingLocalizationAcyclic

/-! # Abstract Čech acyclicity from an extension property

We work in the abstract setting of `CechAlternatingLocalizationAcyclic.lean` (a preorder `P`, a
family of modules `N(v)`, functorial restriction maps `res`, `V(σ) ∈ P` for strictly increasing
index tuples `σ`, with `V(τ) ≤ V(τ with one index removed)`). Assume the *extension property*: for
`σ`, `j ∉ σ`, a finite set of indices `J` (disjoint from `σ`, `j ∉ J`) and `y ∈ N(V(σ ∪ {j}))`
whose restriction to `V(σ ∪ {j, i})` vanishes for every `i ∈ J`, there is `x ∈ N(V(σ))` restricting
to `y` on `V(σ ∪ {j})` and to `0` on `V(σ ∪ {i})` for every `i ∈ J`. Then the alternating Čech
complex is exact in all positive degrees: `p ≥ 0`, `s ∈ C^{p+1}`, `d s = 0` ⇒ `s = d t` for some
`t ∈ C^p`. (For a flasque sheaf `F`, `N(v) = F(v)`, `V(σ) = U_{σ_0} ∩ ⋯ ∩ U_{σ_p}`, the extension
property follows by gluing `y` and `0` on `(U_σ ∩ U_j) ∪ ⋃_{i∈J}(U_σ ∩ U_i)` and extending to `U_σ`
by flasqueness.)

Proof sketch:
1. Induction on a set of indices `K`, proving `C(K)`: every cocycle `s` satisfying the invariant
   `Inv(Kᶜ, s)` := "for `i ∈ Kᶜ`: `s_τ = 0` if `i ∈ τ`, and `s_τ` restricts to zero on `V(τ ∪ {i})` if
   `i ∉ τ`" is a coboundary.
2. `K = ∅`: `Kᶜ` is everything; taking `i = τ_0` gives `s = 0 = d 0`.
3. `K = K' ∪ {j}` (`j ∉ K'`), `J := Kᶜ`. For `j ∉ σ`: if `J` meets `σ`, take `x_σ = 0` (then
   `s_{σ ∪ {j}} = 0` by the invariant); otherwise use the extension property to choose `x_σ` with
   `res x_σ = s_{σ∪{j}}` and vanishing restriction to `V(σ ∪ {i})` for `i ∈ J`. Let `t` be the
   contracting-homotopy cochain of `CechAlternatingLocalizationAcyclic.lean` (with `c = 1`) and
   `s' = s − d t`. Then `d s' = 0`; the invariant for `j` follows from cases A and B of that lemma;
   for `i ∈ J`, every term of `(d t)_τ` is a restriction of some `x_σ` (or `0`), which vanishes after
   factoring through `V(σ ∪ {i})`. Hence `Inv(K'ᶜ, s')`, so `s' = d t'` by induction and
   `s = d(t' + t)`.
4. `K` = everything: `Inv(∅, s)` holds trivially.

Source: the standard argument (Čech acyclicity of flasque sheaves, cutting down the support of a
cocycle index by index with a contracting homotopy).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace CechAltAlg

section Flasque

variable {A : Type*} [CommRing A] {n : ℕ}
  {P : Type*} [Preorder P] (V : ∀ p : ℕ, (Fin (p + 1) ↪o Fin n) → P)
  (N : P → Type*) [∀ v, AddCommGroup (N v)] [∀ v, Module A (N v)]
  (res : ∀ {v w : P}, w ≤ v → N v →ₗ[A] N w)
  (hface : ∀ (p : ℕ) (τ : Fin (p + 2) ↪o Fin n) (k : Fin (p + 2)), V (p + 1) τ ≤ V p (face τ k))

theorem transport_zero {q : ℕ} {τ₁ τ₂ : Fin (q + 1) ↪o Fin n} (e : τ₁ = τ₂) {v : P}
    (h₁ : V q τ₁ ≤ v) (h₂ : V q τ₂ ≤ v) (x : N v) (H : res h₁ x = 0) : res h₂ x = 0 := by
  subst e
  exact H

/-- The invariant: `s` has "empty support" in the directions of the indices in `J`. -/
def Inv (p : ℕ) (J : Finset (Fin n)) (s : Cochain V N p) : Prop :=
  (∀ (τ : Fin (p + 1) ↪o Fin n), ∀ i ∈ J, i ∈ Set.range τ → s τ = 0) ∧
  (∀ (τ : Fin (p + 1) ↪o Fin n), ∀ i ∈ J, ∀ hi : i ∉ Set.range τ,
    res (le_ins V hface p τ i hi) (s τ) = 0)

variable (hcomp : ∀ {u v w : P} (h : v ≤ u) (h' : w ≤ v) (x : N u),
    res h' (res h x) = res (h'.trans h) x)
  (hext : ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ)
    (J : Finset (Fin n)), j ∉ J → (∀ i ∈ J, i ∉ Set.range σ) →
    ∀ y : N (V (p + 1) (ins σ j hj)),
    (∀ i ∈ J, ∀ hi : i ∉ Set.range (ins σ j hj),
      res (le_ins V hface (p + 1) (ins σ j hj) i hi) y = 0) →
    ∃ x : N (V p σ), res (le_ins V hface p σ j hj) x = y ∧
      ∀ i ∈ J, ∀ hi : i ∉ Set.range σ, res (le_ins V hface p σ i hi) x = 0)

include hcomp hext in
theorem flasque_step (p : ℕ) (J : Finset (Fin n)) (j : Fin n) (hjJ : j ∉ J)
    (s : Cochain V N (p + 1))
    (hs : d V N res hface (p + 1) s = 0) (hInv : Inv V N res hface (p + 1) J s) :
    ∃ t : Cochain V N p, Inv V N res hface (p + 1) (insert j J) (s - d V N res hface p t) := by
  classical
  -- choose `x`
  have hex : ∀ (σ : Fin (p + 1) ↪o Fin n) (hj : j ∉ Set.range σ),
      ∃ x : N (V p σ), res (le_ins V hface p σ j hj) x = (1 : A) • s (ins σ j hj) ∧
        (∀ i ∈ J, i ∈ Set.range σ → x = 0) ∧
        (∀ i ∈ J, ∀ hi : i ∉ Set.range σ, res (le_ins V hface p σ i hi) x = 0) := by
    intro σ hj
    by_cases hJ : ∃ i ∈ J, i ∈ Set.range σ
    · obtain ⟨i, hiJ, hiσ⟩ := hJ
      refine ⟨0, ?_, fun _ _ _ => rfl, fun _ _ _ => map_zero _⟩
      have hi' : i ∈ Set.range (ins σ j hj) := by
        rw [range_ins]
        exact Or.inr hiσ
      rw [map_zero, hInv.1 _ i hiJ hi', smul_zero]
    · push Not at hJ
      obtain ⟨x, hx1, hx2⟩ := hext p σ j hj J hjJ hJ (s (ins σ j hj))
        (fun i hiJ hi => hInv.2 _ i hiJ hi)
      exact ⟨x, by rw [hx1, one_smul], fun i hiJ hiσ => absurd hiσ (hJ i hiJ), hx2⟩
  choose x hx1 hx2 hx3 using hex
  refine ⟨homotopyCochain V N p j x, ?_, ?_⟩
  · intro τ i hi hiτ
    rw [Pi.sub_apply]
    rcases Finset.mem_insert.1 hi with rfl | hiJ
    · rw [homotopy_step_mem V N res hface p s i 1 x hx1 τ hiτ, one_smul, sub_self]
    · rw [hInv.1 τ i hiJ hiτ, zero_sub, neg_eq_zero, d_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hjf : j ∈ Set.range (face τ k)
      · rw [homotopyCochain_mem V N p j x _ hjf, map_zero, smul_zero]
      · rw [homotopyCochain_not_mem V N p j x _ hjf, map_zsmul]
        by_cases hif : i ∈ Set.range (face τ k)
        · rw [hx2 _ hjf i hiJ hif, map_zero, smul_zero, smul_zero]
        · have hik : i = τ k := by
            rw [range_face] at hif
            by_contra hne
            exact hif ⟨hiτ, hne⟩
          subst hik
          rw [transport_zero V N res (ins_face_self τ k) (le_ins V hface p (face τ k) (τ k) hif)
            (hface p τ k) _ (hx3 _ hjf (τ k) hiJ hif), smul_zero, smul_zero]
  · intro τ i hi hiτ
    rw [Pi.sub_apply, map_sub]
    rcases Finset.mem_insert.1 hi with rfl | hiJ
    · rw [homotopy_step_not_mem V N res hface hcomp p s hs i 1 x hx1 τ hiτ, one_smul, sub_self]
    · rw [hInv.2 τ i hiJ hiτ, zero_sub, neg_eq_zero, d_apply, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [map_zsmul, hcomp]
      by_cases hjf : j ∈ Set.range (face τ k)
      · rw [homotopyCochain_mem V N p j x _ hjf, map_zero, smul_zero]
      · have hif : i ∉ Set.range (face τ k) := not_mem_face hiτ k
        have hle : V (p + 2) (ins τ i hiτ) ≤ V (p + 1) (ins (face τ k) i hif) := by
          rw [ins_face]
          exact hface (p + 1) (ins τ i hiτ) _
        rw [homotopyCochain_not_mem V N p j x _ hjf, map_zsmul,
          ← hcomp (le_ins V hface p (face τ k) i hif) hle, hx3 _ hjf i hiJ hif, map_zero,
          smul_zero, smul_zero]

include hcomp hext in
/-- The extension property ⇒ the alternating Čech complex is exact in all positive degrees. -/
theorem exists_d_eq_of_ext (p : ℕ) (s : Cochain V N (p + 1))
    (hs : d V N res hface (p + 1) s = 0) : ∃ t : Cochain V N p, d V N res hface p t = s := by
  classical
  have C : ∀ K : Finset (Fin n), ∀ s : Cochain V N (p + 1), d V N res hface (p + 1) s = 0 →
      Inv V N res hface (p + 1) Kᶜ s → ∃ t : Cochain V N p, d V N res hface p t = s := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro s _ hInv
      refine ⟨0, ?_⟩
      rw [map_zero]
      funext τ
      exact (hInv.1 τ (τ 0) (by simp) ⟨0, rfl⟩).symm
    | insert j K' hj ih =>
      intro s hs hInv
      obtain ⟨t, ht⟩ := flasque_step V N res hface hcomp hext p (insert j K')ᶜ j
        (by simp) s hs hInv
      have hK : insert j (insert j K')ᶜ = K'ᶜ := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_compl, not_or]
        constructor
        · rintro (rfl | h)
          · exact hj
          · exact h.2
        · intro h
          by_cases hij : i = j
          · exact Or.inl hij
          · exact Or.inr ⟨hij, h⟩
      rw [hK] at ht
      obtain ⟨t', ht'⟩ := ih (s - d V N res hface p t)
        (by rw [map_sub, hs, d_comp_d V N res hface hcomp, sub_zero]) ht
      exact ⟨t' + t, by rw [map_add, ht', sub_add_cancel]⟩
  refine C Finset.univ s hs ?_
  rw [Finset.compl_univ]
  exact ⟨fun _ i hi => absurd hi (Finset.notMem_empty i), fun _ i hi => absurd hi (Finset.notMem_empty i)⟩

end Flasque

end CechAltAlg

end
