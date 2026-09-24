import MiyaokaMori.Prelude

/-! # Acyclicity of the alternating Čech complex of localizations

Let `A` be a commutative ring and `f_1, …, f_n ∈ A` generate the unit ideal. Given a family of
`A`-modules `N(v)` (`v` in a preorder `P`) with functorial `A`-linear restriction maps
`res : N(v) → N(w)` (`w ≤ v`), and for every strictly increasing index tuple `σ = (i_0 < ⋯ < i_p)`
an element `V(σ) ∈ P` with `V(τ) ≤ V(τ with one index removed)`, such that for `j ∉ σ` the restriction
`N(V(σ)) → N(V(σ ∪ {j}))` has the two "localization at `f_j`" properties (every element lifts after
multiplication by a power of `f_j`; an element restricting to zero is killed by a power of `f_j`).
Then the alternating (ordered) Čech complex `C^p = ∏_{i_0<⋯<i_p} N(V(i_0 … i_p))`,
`d(s)_τ = Σ_k (-1)^k res(s_{τ minus the k-th index})`, is exact in all positive degrees: `p ≥ 0`,
`s ∈ C^{p+1}`, `d s = 0` ⇒ `s = d t` for some `t ∈ C^p`. Special case: `N(V(σ)) = M_{f_{i_0} ⋯ f_{i_p}}`
for an `A`-module `M` gives exactness in positive degrees of the localization Čech complex
`0 → M → ∏ M_{f_i} → ∏ M_{f_i f_j} → ⋯`.

Proof sketch:
1. (Combinatorics) For `σ : Fin m ↪o Fin n` and `j ∉ σ`, define the insertion
   `ins σ j : Fin (m+1) ↪o Fin n` (range = range of `σ` ∪ `{j}`, via `Finset.orderEmbOfFin`) and the
   position `pos` of `j`; a strictly increasing map is determined by its range (`StrictMono.range_inj`),
   so `(ins σ j)` minus the `pos`-th index is `σ`; `ins (τ minus l') j = (ins τ j) minus l` with
   `l = pos.succAbove l'`; positions satisfy `pos τ = l.succAbove (pos (τ minus l'))`, whence
   `pos(τ minus l') + l' + 1 = pos τ + l` (parity lemma).
2. (Contracting homotopy for fixed `j`, elementwise) Let `d s = 0`. By surjectivity of localization
   and finiteness of the index set, choose a uniform `m` and `x_σ ∈ N(V(σ))` (`j ∉ σ`) with
   `res(x_σ) = f_j^m • s_{ins σ j}`. Set `t_σ = (-1)^{pos σ} x_σ` (`j ∉ σ`), `t_σ = 0` (`j ∈ σ`).
   (A) If `j = τ_{k0}`: only the term `k = k0` of `(d t)_τ` is nonzero (the other faces still contain
   `j`), and it equals `(-1)^{k0} (-1)^{k0} res(x) = f_j^m • s_τ`.
   (B) If `j ∉ τ`: let `τ' = ins τ j`, `k = pos τ`. Restricting `(d t)_τ` to `V(τ')` and using the
   commutation relations and parity of step 1,
   `res((d t)_τ) = -(-1)^k f_j^m Σ_{l ≠ k} (-1)^l res(s_{τ' minus l})`, while the cocycle condition
   `(d s)_{τ'} = 0` gives `Σ_{l≠k} (-1)^l res(s_{τ' minus l}) = -(-1)^k res(s_τ)`; hence
   `res((d t)_τ − f_j^m s_τ) = 0`, and by the kernel property of localization it is killed by a power
   of `f_j`. With a uniform `m'`, `d(f_j^{m'} t) = f_j^{m+m'} • s`.
3. (Partition of unity) For each `j` this gives `m_j`, `t_j` with `d t_j = f_j^{m_j} s`; with a
   uniform exponent `M`, `Ideal.span_pow_eq_top` gives `1 = Σ c_j f_j^M`, so `d(Σ c_j t_j) = s`.
4. (Additionally) `d ∘ d = 0` in the same setting (`d_comp_d`): apply `Finset.sum_ninvolution` to
   `(k, l) ↦ (k.succAbove l, l.predAbove k)`; the face maps commute by
   `Fin.succAbove_succAbove_succAbove_predAbove`, and the signs are opposite by the parity lemma of
   step 1. Cases A and B of step 2 are stated separately as `homotopy_step_mem`,
   `homotopy_step_not_mem` (with an arbitrary scalar `c`) for reuse in
   `CechAlternatingFlasqueAcyclic.lean`.

Source: the proofs of Stacks 01X8 / 01X9 (contracting homotopy after localization + partition of
unity).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace CechAltAlg

/-! ## Combinatorics: insertion into strictly increasing index tuples, and face maps -/

section Comb

variable {m n : ℕ}

/-- Remove the `k`-th index. -/
abbrev face (τ : Fin (m + 1) ↪o Fin n) (k : Fin (m + 1)) : Fin m ↪o Fin n :=
  (Fin.succAboveOrderEmb k).trans τ

theorem emb_ext {σ σ' : Fin m ↪o Fin n} (h : Set.range σ = Set.range σ') : σ = σ' :=
  DFunLike.coe_injective ((σ.strictMono.range_inj σ'.strictMono).1 h)

theorem range_face (τ : Fin (m + 1) ↪o Fin n) (k : Fin (m + 1)) :
    Set.range (face τ k) = Set.range τ \ {τ k} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    intro h
    exact Fin.succAbove_ne k i (τ.injective h)
  · rintro ⟨⟨i, rfl⟩, hi⟩
    have hik : i ≠ k := by
      rintro rfl
      exact hi rfl
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hik
    exact ⟨i', rfl⟩

theorem not_mem_face {τ : Fin (m + 1) ↪o Fin n} {j : Fin n} (hj : j ∉ Set.range τ)
    (k : Fin (m + 1)) : j ∉ Set.range (face τ k) := by
  rw [range_face]
  exact fun h => hj h.1

theorem card_insert_range (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) :
    (insert j (Finset.univ.map σ.toEmbedding)).card = m + 1 := by
  rw [Finset.card_insert_of_notMem, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_map.1 h
  exact hj ⟨i, hi⟩

/-- Insert `j` into the strictly increasing index tuple `σ`. -/
def ins (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) : Fin (m + 1) ↪o Fin n :=
  (insert j (Finset.univ.map σ.toEmbedding)).orderEmbOfFin (card_insert_range σ j hj)

theorem range_ins (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) :
    Set.range (ins σ j hj) = insert j (Set.range σ) := by
  rw [ins, Finset.range_orderEmbOfFin]
  ext x
  simp

theorem exists_pos (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) :
    ∃ k, ins σ j hj k = j := by
  have : j ∈ Set.range (ins σ j hj) := by
    rw [range_ins]
    exact Set.mem_insert _ _
  exact this

/-- The position of `j` in `ins σ j`. -/
def pos (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) : Fin (m + 1) :=
  Classical.choose (exists_pos σ j hj)

theorem ins_pos (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) :
    ins σ j hj (pos σ j hj) = j :=
  Classical.choose_spec (exists_pos σ j hj)

theorem face_ins (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) :
    face (ins σ j hj) (pos σ j hj) = σ := by
  apply emb_ext
  rw [range_face, range_ins, ins_pos]
  ext x
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    · exact h1
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rintro rfl
    exact hj h

theorem ins_succAbove (σ : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) (i : Fin m) :
    ins σ j hj ((pos σ j hj).succAbove i) = σ i :=
  congrArg (fun e : Fin m ↪o Fin n => e i) (face_ins σ j hj)

theorem ins_face (τ : Fin (m + 1) ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range τ)
    (l' : Fin (m + 1)) :
    ins (face τ l') j (not_mem_face hj l') = face (ins τ j hj) ((pos τ j hj).succAbove l') := by
  apply emb_ext
  rw [range_ins, range_face, range_face, range_ins, ins_succAbove]
  have hne : j ≠ τ l' := fun h => hj ⟨l', h.symm⟩
  ext x
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact ⟨Or.inl h, by rw [h]; exact hne⟩
    · exact ⟨Or.inr h1, h2⟩
  · rintro ⟨h | h, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, h2⟩

theorem pos_face (τ : Fin (m + 1) ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range τ)
    (l' : Fin (m + 1)) :
    pos τ j hj =
      ((pos τ j hj).succAbove l').succAbove (pos (face τ l') j (not_mem_face hj l')) := by
  apply (ins τ j hj).injective
  rw [ins_pos]
  have h := ins_pos (face τ l') j (not_mem_face hj l')
  rw [ins_face] at h
  exact h.symm

theorem parity {k l : Fin (m + 2)} {l' k'' : Fin (m + 1)} (hl : l = k.succAbove l')
    (hk : k = l.succAbove k'') : (k'' : ℕ) + l' + 1 = k + l := by
  have h1 : ((l : ℕ) = l' ∧ (l' : ℕ) < k) ∨ ((l : ℕ) = l' + 1 ∧ (k : ℕ) ≤ l') := by
    rw [hl]
    by_cases h : l'.castSucc < k
    · left
      rw [Fin.succAbove_of_castSucc_lt _ _ h]
      exact ⟨rfl, h⟩
    · right
      rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 h)]
      exact ⟨rfl, not_lt.1 h⟩
  have h2 : ((k : ℕ) = k'' ∧ (k'' : ℕ) < l) ∨ ((k : ℕ) = k'' + 1 ∧ (l : ℕ) ≤ k'') := by
    have : (k : ℕ) = (l.succAbove k'' : Fin (m + 2)) := by rw [← hk]
    rw [this]
    by_cases h : k''.castSucc < l
    · left
      rw [Fin.succAbove_of_castSucc_lt _ _ h]
      exact ⟨rfl, h⟩
    · right
      rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 h)]
      exact ⟨rfl, not_lt.1 h⟩
  omega

/-- If `j = τ k0`, then `τ` minus the `k0`-th index does not contain `j`. -/
theorem not_mem_face_self (τ : Fin (m + 1) ↪o Fin n) (k0 : Fin (m + 1)) :
    τ k0 ∉ Set.range (face τ k0) := by
  rw [range_face]
  exact fun h => h.2 rfl

theorem ins_face_self (τ : Fin (m + 1) ↪o Fin n) (k0 : Fin (m + 1)) :
    ins (face τ k0) (τ k0) (not_mem_face_self τ k0) = τ := by
  apply emb_ext
  rw [range_ins, range_face]
  ext x
  constructor
  · rintro (h | h)
    · exact ⟨k0, h.symm⟩
    · exact h.1
  · intro h
    by_cases hx : x = τ k0
    · exact Or.inl hx
    · exact Or.inr ⟨h, hx⟩

theorem pos_face_self (τ : Fin (m + 1) ↪o Fin n) (k0 : Fin (m + 1)) :
    pos (face τ k0) (τ k0) (not_mem_face_self τ k0) = k0 := by
  have h := ins_pos (face τ k0) (τ k0) (not_mem_face_self τ k0)
  have e := ins_face_self τ k0
  apply τ.injective
  calc τ (pos (face τ k0) (τ k0) (not_mem_face_self τ k0))
      = ins (face τ k0) (τ k0) (not_mem_face_self τ k0)
          (pos (face τ k0) (τ k0) (not_mem_face_self τ k0)) := by rw [e]
    _ = τ k0 := h

theorem mem_face_of_ne (τ : Fin (m + 1) ↪o Fin n) {k0 k : Fin (m + 1)} (h : k ≠ k0) :
    τ k0 ∈ Set.range (face τ k) := by
  rw [range_face]
  exact ⟨⟨k0, rfl⟩, fun h' => h (τ.injective h').symm⟩

end Comb

/-! ## Algebra -/

section Alg

theorem uniform_exponent {ι : Type*} [Finite ι] (Q : ι → ℕ → Prop)
    (mono : ∀ i a b, a ≤ b → Q i a → Q i b) (h : ∀ i, ∃ a, Q i a) : ∃ a, ∀ i, Q i a := by
  cases nonempty_fintype ι
  choose g hg using h
  exact ⟨Finset.univ.sup g, fun i => mono i _ _ (Finset.le_sup (Finset.mem_univ i)) (hg i)⟩

variable {A : Type*} [CommRing A] {n : ℕ} (f : Fin n → A)
  {P : Type*} [Preorder P] (V : ∀ p : ℕ, (Fin (p + 1) ↪o Fin n) → P)
  (N : P → Type*) [∀ v, AddCommGroup (N v)] [∀ v, Module A (N v)]
  (res : ∀ {v w : P}, w ≤ v → N v →ₗ[A] N w)
  (hface : ∀ (p : ℕ) (τ : Fin (p + 2) ↪o Fin n) (k : Fin (p + 2)), V (p + 1) τ ≤ V p (face τ k))

/-- Alternating Čech cochains. -/
abbrev Cochain (p : ℕ) : Type _ := ∀ σ : Fin (p + 1) ↪o Fin n, N (V p σ)

/-- The alternating Čech differential. -/
def d (p : ℕ) : Cochain V N p →ₗ[A] Cochain V N (p + 1) :=
  LinearMap.pi fun τ => ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    ((res (hface p τ k)).comp (LinearMap.proj (face τ k)))

theorem d_apply (p : ℕ) (s : Cochain V N p) (τ : Fin (p + 2) ↪o Fin n) :
    d V N res hface p s τ =
      ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • res (hface p τ k) (s (face τ k)) := by
  simp [d, LinearMap.sum_apply]

include hface in
theorem le_ins (p : ℕ) (σ : Fin (p + 1) ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ) :
    V (p + 1) (ins σ j hj) ≤ V p σ := by
  have h := hface p (ins σ j hj) (pos σ j hj)
  rwa [face_ins] at h

theorem transport_res {q : ℕ} (s : Cochain V N q)
    {σ₁ σ₂ : Fin (q + 1) ↪o Fin n} (e : σ₁ = σ₂) {w : P} (h₁ : w ≤ V q σ₁) (h₂ : w ≤ V q σ₂) :
    res h₁ (s σ₁) = res h₂ (s σ₂) := by
  subst e
  rfl

theorem transport_eq {q : ℕ} (s : Cochain V N q)
    {τ₁ τ₂ : Fin (q + 1) ↪o Fin n} (e : τ₁ = τ₂) {v : P} (h₁ : V q τ₁ ≤ v) (h₂ : V q τ₂ ≤ v)
    (x : N v) (c : A) (H : res h₁ x = c • s τ₁) : res h₂ x = c • s τ₂ := by
  subst e
  exact H

variable (hcomp : ∀ {u v w : P} (h : v ≤ u) (h' : w ≤ v) (x : N u),
    res h' (res h x) = res (h'.trans h) x)
  (hloc : ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range σ)
    (h : V (p + 1) (ins σ j hj) ≤ V p σ),
    (∀ y : N (V (p + 1) (ins σ j hj)), ∃ (m : ℕ) (x : N (V p σ)), res h x = f j ^ m • y) ∧
    (∀ x : N (V p σ), res h x = 0 → ∃ m : ℕ, f j ^ m • x = 0))

instance (a b : ℕ) : Finite (Fin a ↪o Fin b) :=
  Finite.of_injective (fun σ => (σ : Fin a → Fin b)) DFunLike.coe_injective

theorem sign_sq (a : ℕ) : ((-1 : ℤ) ^ a) * ((-1 : ℤ) ^ a) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem face_face {m : ℕ} (τ : Fin (m + 2) ↪o Fin n) (k : Fin (m + 2)) (l : Fin (m + 1)) :
    face (face τ (k.succAbove l)) (l.predAbove k) = face (face τ k) l := by
  apply RelEmbedding.ext
  intro i
  show τ ((k.succAbove l).succAbove ((l.predAbove k).succAbove i)) = τ (k.succAbove (l.succAbove i))
  rw [Fin.succAbove_succAbove_succAbove_predAbove]

theorem sign_swap {m : ℕ} (k : Fin (m + 2)) (l : Fin (m + 1)) :
    ((-1 : ℤ) ^ ((k.succAbove l : Fin (m + 2)) : ℕ)) * ((-1 : ℤ) ^ ((l.predAbove k : Fin (m + 1)) : ℕ)) =
      -(((-1 : ℤ) ^ (k : ℕ)) * ((-1 : ℤ) ^ (l : ℕ))) := by
  have hp := parity (k := k) (l := k.succAbove l) (l' := l) (k'' := l.predAbove k) rfl
    (Fin.succAbove_succAbove_predAbove k l).symm
  have h2 : ((k.succAbove l : Fin (m + 2)) : ℕ) + (l.predAbove k : Fin (m + 1)) + (k + l) =
      2 * ((l : ℕ) + (l.predAbove k : Fin (m + 1))) + 1 := by omega
  have h3 : ((-1 : ℤ) ^ ((k.succAbove l : Fin (m + 2)) : ℕ) *
      (-1 : ℤ) ^ ((l.predAbove k : Fin (m + 1)) : ℕ)) * ((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) = -1 := by
    rw [← pow_add, ← pow_add, ← pow_add, h2, pow_succ, pow_mul]
    simp
  have h4 := sign_sq ((k : ℕ) + l)
  rw [pow_add] at h4
  calc _ = ((-1 : ℤ) ^ ((k.succAbove l : Fin (m + 2)) : ℕ) *
        (-1 : ℤ) ^ ((l.predAbove k : Fin (m + 1)) : ℕ)) *
        (((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) * ((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ))) := by
        rw [h4, mul_one]
    _ = _ := by rw [← mul_assoc, h3, neg_one_mul]

include hcomp in
/-- `d ∘ d = 0`. -/
theorem d_comp_d (p : ℕ) (s : Cochain V N p) :
    d V N res hface (p + 1) (d V N res hface p s) = 0 := by
  funext τ
  rw [d_apply]
  have hterm : ∀ k : Fin (p + 3),
      ((-1 : ℤ) ^ (k : ℕ)) • res (hface (p + 1) τ k) (d V N res hface p s (face τ k)) =
        ∑ l : Fin (p + 2), (((-1 : ℤ) ^ (k : ℕ)) * ((-1 : ℤ) ^ (l : ℕ))) •
          res ((hface (p + 1) τ k).trans (hface p (face τ k) l)) (s (face (face τ k) l)) := by
    intro k
    rw [d_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, hcomp, smul_smul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_product']
  refine Finset.sum_ninvolution (fun a => (a.1.succAbove a.2, a.2.predAbove a.1)) ?_ ?_ ?_ ?_
  · rintro ⟨k, l⟩
    dsimp only
    rw [sign_swap, neg_smul,
      transport_res V N res s (face_face τ k l)
        ((hface (p + 1) τ (k.succAbove l)).trans (hface p (face τ (k.succAbove l)) (l.predAbove k)))
        ((hface (p + 1) τ k).trans (hface p (face τ k) l)), add_neg_cancel]
  · rintro ⟨k, l⟩ _ h
    exact Fin.succAbove_ne k l (congrArg Prod.fst h)
  · intro a
    exact Finset.mem_univ _
  · rintro ⟨k, l⟩
    refine Prod.ext (Fin.succAbove_succAbove_predAbove k l) ?_
    apply Fin.succAbove_right_injective (p := k)
    have := Fin.succAbove_succAbove_predAbove (k.succAbove l) (l.predAbove k)
    rw [Fin.succAbove_succAbove_predAbove k l] at this
    exact this

/-- The contracting-homotopy cochain: `t_σ = (-1)^{pos σ j} x_σ` (`j ∉ σ`), `t_σ = 0` (`j ∈ σ`). -/
def homotopyCochain (p : ℕ) (j : Fin n)
    (x : ∀ σ : Fin (p + 1) ↪o Fin n, j ∉ Set.range σ → N (V p σ)) : Cochain V N p := by
  classical
  exact fun σ => if hj : j ∈ Set.range σ then 0 else ((-1 : ℤ) ^ (pos σ j hj : ℕ)) • x σ hj

omit [∀ v, Module A (N v)] [Preorder P] in
theorem homotopyCochain_mem (p : ℕ) (j : Fin n)
    (x : ∀ σ : Fin (p + 1) ↪o Fin n, j ∉ Set.range σ → N (V p σ))
    (σ : Fin (p + 1) ↪o Fin n) (hj : j ∈ Set.range σ) : homotopyCochain V N p j x σ = 0 := by
  classical
  exact dif_pos hj

omit [∀ v, Module A (N v)] [Preorder P] in
theorem homotopyCochain_not_mem (p : ℕ) (j : Fin n)
    (x : ∀ σ : Fin (p + 1) ↪o Fin n, j ∉ Set.range σ → N (V p σ))
    (σ : Fin (p + 1) ↪o Fin n) (hj : j ∉ Set.range σ) :
    homotopyCochain V N p j x σ = ((-1 : ℤ) ^ (pos σ j hj : ℕ)) • x σ hj := by
  classical
  exact dif_neg hj

/-- Case A: if `j ∈ τ`, then `(d t)_τ = c • s_τ`. -/
theorem homotopy_step_mem (p : ℕ) (s : Cochain V N (p + 1)) (j : Fin n) (c : A)
    (x : ∀ σ : Fin (p + 1) ↪o Fin n, j ∉ Set.range σ → N (V p σ))
    (hx : ∀ σ hj, res (le_ins V hface p σ j hj) (x σ hj) = c • s (ins σ j hj))
    (τ : Fin (p + 2) ↪o Fin n) (hj : j ∈ Set.range τ) :
    d V N res hface p (homotopyCochain V N p j x) τ = c • s τ := by
  obtain ⟨k0, hk0⟩ := hj
  subst hk0
  rw [d_apply, Finset.sum_eq_single k0]
  · rw [homotopyCochain_not_mem V N p (τ k0) x (face τ k0) (not_mem_face_self τ k0),
      map_zsmul, smul_smul, pos_face_self, sign_sq, one_smul]
    exact transport_eq V N res s (ins_face_self τ k0) _ _ _ _
      (hx (face τ k0) (not_mem_face_self τ k0))
  · intro k _ hk
    rw [homotopyCochain_mem V N p (τ k0) x (face τ k) (mem_face_of_ne τ hk), map_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

include hcomp in
/-- Case B: if `j ∉ τ`, then `(d t)_τ` and `c • s_τ` agree after restriction to `V(τ ∪ {j})` (uses
the cocycle condition). -/
theorem homotopy_step_not_mem (p : ℕ) (s : Cochain V N (p + 1))
    (hs : d V N res hface (p + 1) s = 0) (j : Fin n) (c : A)
    (x : ∀ σ : Fin (p + 1) ↪o Fin n, j ∉ Set.range σ → N (V p σ))
    (hx : ∀ σ hj, res (le_ins V hface p σ j hj) (x σ hj) = c • s (ins σ j hj))
    (τ : Fin (p + 2) ↪o Fin n) (hj : j ∉ Set.range τ) :
    res (le_ins V hface (p + 1) τ j hj) (d V N res hface p (homotopyCochain V N p j x) τ) =
      c • res (le_ins V hface (p + 1) τ j hj) (s τ) := by
  have h := le_ins V hface (p + 1) τ j hj
  have hterm : ∀ l' : Fin (p + 2),
      ((-1 : ℤ) ^ (l' : ℕ)) • res h (res (hface p τ l') (homotopyCochain V N p j x (face τ l'))) =
        (-((-1 : ℤ) ^ (pos τ j hj : ℕ))) • c •
          (((-1 : ℤ) ^ (((pos τ j hj).succAbove l' : Fin (p + 3)) : ℕ)) •
            res (hface (p + 1) (ins τ j hj) ((pos τ j hj).succAbove l'))
              (s (face (ins τ j hj) ((pos τ j hj).succAbove l')))) := by
    intro l'
    have hle : V (p + 2) (ins τ j hj) ≤ V (p + 1) (ins (face τ l') j (not_mem_face hj l')) := by
      rw [ins_face]
      exact hface (p + 1) (ins τ j hj) _
    have e1 : res h (res (hface p τ l') (x (face τ l') (not_mem_face hj l'))) =
        c • res (hface (p + 1) (ins τ j hj) ((pos τ j hj).succAbove l'))
          (s (face (ins τ j hj) ((pos τ j hj).succAbove l'))) := by
      rw [hcomp, ← hcomp (le_ins V hface p (face τ l') j (not_mem_face hj l')) hle,
        hx (face τ l') (not_mem_face hj l'), map_smul,
        transport_res V N res s (ins_face τ j hj l') hle
          (hface (p + 1) (ins τ j hj) ((pos τ j hj).succAbove l'))]
    have hsign : ((-1 : ℤ) ^ (l' : ℕ)) *
        ((-1 : ℤ) ^ (pos (face τ l') j (not_mem_face hj l') : ℕ)) =
        (-((-1 : ℤ) ^ (pos τ j hj : ℕ))) *
          ((-1 : ℤ) ^ (((pos τ j hj).succAbove l' : Fin (p + 3)) : ℕ)) := by
      have hp := parity (k := pos τ j hj) (l := (pos τ j hj).succAbove l') (l' := l')
        (k'' := pos (face τ l') j (not_mem_face hj l')) rfl (pos_face τ j hj l')
      rw [neg_mul, ← pow_add, ← pow_add, ← hp, pow_succ, mul_neg_one, neg_neg, add_comm]
    rw [homotopyCochain_not_mem V N p j x (face τ l') (not_mem_face hj l'),
      map_zsmul, map_zsmul, e1, smul_smul, hsign,
      smul_comm c ((-1 : ℤ) ^ (((pos τ j hj).succAbove l' : Fin (p + 3)) : ℕ)),
      smul_smul]
  have hc : ∑ l : Fin (p + 3), ((-1 : ℤ) ^ (l : ℕ)) •
      res (hface (p + 1) (ins τ j hj) l) (s (face (ins τ j hj) l)) = 0 := by
    rw [← d_apply, hs]
    rfl
  rw [Fin.sum_univ_succAbove _ (pos τ j hj), add_eq_zero_iff_neg_eq] at hc
  rw [d_apply, map_sum]
  simp_rw [map_zsmul]
  rw [Finset.sum_congr rfl (fun l' _ => hterm l'), ← Finset.smul_sum, ← Finset.smul_sum, ← hc,
    transport_res V N res s (face_ins τ j hj) (hface (p + 1) (ins τ j hj) (pos τ j hj)) h,
    smul_neg, smul_neg, neg_smul, neg_neg, smul_comm c, smul_smul, sign_sq, one_smul]

include hcomp hloc in
/-- For fixed `j`: a cocycle times a power of `f_j` is a coboundary (elementwise form of the
contracting homotopy after localization). -/
theorem exists_pow_smul_eq_d (p : ℕ) (s : Cochain V N (p + 1))
    (hs : d V N res hface (p + 1) s = 0) (j : Fin n) :
    ∃ (m : ℕ) (t : Cochain V N p), d V N res hface p t = f j ^ m • s := by
  classical
  obtain ⟨m, hm⟩ := uniform_exponent
    (fun (σ : Fin (p + 1) ↪o Fin n) (a : ℕ) => ∀ hj : j ∉ Set.range σ,
      ∃ x : N (V p σ), res (le_ins V hface p σ j hj) x = f j ^ a • s (ins σ j hj))
    (by
      intro σ a b hab h hj
      obtain ⟨x, hx⟩ := h hj
      refine ⟨f j ^ (b - a) • x, ?_⟩
      rw [map_smul, hx, smul_smul, ← pow_add, Nat.sub_add_cancel hab])
    (by
      intro σ
      by_cases hj : j ∈ Set.range σ
      · exact ⟨0, fun h => absurd hj h⟩
      · obtain ⟨a, x, hx⟩ := (hloc p σ j hj (le_ins V hface p σ j hj)).1 (s (ins σ j hj))
        exact ⟨a, fun _ => ⟨x, hx⟩⟩)
  choose x hx using hm
  have key : ∀ τ : Fin (p + 2) ↪o Fin n,
      ∃ a : ℕ, f j ^ a • (d V N res hface p (homotopyCochain V N p j x) τ - f j ^ m • s τ) = 0 := by
    intro τ
    by_cases hj : j ∈ Set.range τ
    · refine ⟨0, ?_⟩
      rw [homotopy_step_mem V N res hface p s j (f j ^ m) x hx τ hj, sub_self, smul_zero]
    · refine (hloc (p + 1) τ j hj (le_ins V hface (p + 1) τ j hj)).2 _ ?_
      rw [map_sub, sub_eq_zero, map_smul]
      exact homotopy_step_not_mem V N res hface hcomp p s hs j (f j ^ m) x hx τ hj
  obtain ⟨a, ha⟩ := uniform_exponent _
    (by
      intro τ a b hab h
      show f j ^ b • (d V N res hface p (homotopyCochain V N p j x) τ - f j ^ m • s τ) = 0
      rw [← Nat.sub_add_cancel hab, pow_add, mul_smul, h, smul_zero]) key
  refine ⟨a + m, f j ^ a • homotopyCochain V N p j x, ?_⟩
  rw [map_smul]
  funext τ
  have := ha τ
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at this
  exact this

include hcomp hloc in
/-- The alternating Čech complex is exact in all positive degrees. -/
theorem exists_d_eq (hspan : Ideal.span (Set.range f) = ⊤) (p : ℕ) (s : Cochain V N (p + 1))
    (hs : d V N res hface (p + 1) s = 0) :
    ∃ t : Cochain V N p, d V N res hface p t = s := by
  classical
  choose m t ht using fun j => exists_pow_smul_eq_d f V N res hface hcomp hloc p s hs j
  have ht' : ∀ j, d V N res hface p (f j ^ (Finset.univ.sup m - m j) • t j) =
      f j ^ (Finset.univ.sup m) • s := by
    intro j
    rw [map_smul, ht, smul_smul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ j))]
  have h1 := Ideal.span_pow_eq_top _ hspan (Finset.univ.sup m)
  rw [← Set.range_comp] at h1
  have h2 : (1 : A) ∈ Ideal.span (Set.range ((fun x => x ^ Finset.univ.sup m) ∘ f)) := by
    rw [h1]
    trivial
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h2
  refine ⟨∑ j, c j • (f j ^ (Finset.univ.sup m - m j) • t j), ?_⟩
  rw [map_sum, Finset.sum_congr rfl (fun j _ => by
    rw [map_smul, ht' j, smul_smul] :
      ∀ j ∈ Finset.univ, d V N res hface p (c j • (f j ^ (Finset.univ.sup m - m j) • t j)) =
        (c j * f j ^ Finset.univ.sup m) • s), ← Finset.sum_smul]
  simp only [Function.comp] at hc
  rw [hc, one_smul]

end Alg

end CechAltAlg

end
