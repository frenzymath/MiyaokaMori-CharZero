import MiyaokaMori.Prelude

/-! # Stacks 00LN: regular sequences are quasi-regular

Stacks 00LN(1): in any commutative ring `R`, a regular sequence `f_1..f_c` is quasi-regular — if a homogeneous
polynomial `F` of degree `n` satisfies `F(f) ∈ J^{n+1}` (`J = (f_1..f_c)`), then all coefficients of `F` lie in `J`.

References: Stacks 00LN (algebra-lemma-regular-quasi-regular) (1); the same theorem is Matsumura, *Commutative Ring
Theory*, Thm 16.2(i). The definition of quasi-regular is the elementwise form of Stacks 061P
(algebra-definition-quasi-regular-sequence).

## Route
The proof of Stacks is "induction on `c` + induction on the highest power `l` of `f_c`"; here we follow the
arrangement of Matsumura 16.2(i) (the same double induction, with the inner induction on the degree `n`, peeling off
one layer `F = G + X·H` at a time, so that the full expansion `Σ_e G_e X^e` never has to be handled). The
step-by-step correspondence is in the docstring of `IsQuasiRegularFamily.of_tail`.
* The element peeled off is the **last** one of the sequence; Mathlib's `MvPolynomial.finSuccEquiv` family peels off
  the variable `X 0`, so the core induction uses the "reversed" condition (`f i` regular modulo the **later** elements),
  and `Fin.rev` converts back at the end (quasi-regularity does not depend on the order of the variables).
* Mathlib has `Ideal.mem_span_pow_iff_exists_isHomogeneous`:
  `y ∈ span (range x) ^ n ↔ ∃ p, p.IsHomogeneous n ∧ eval x p = y`.

Structure: definition → `mem_pow_of_mul_mem_pow` (Matsumura's claim) → `of_tail` (induction step) →
`isQuasiRegularFamily_of_regular_mod_later` (induction on `c`) → the main theorem
`RingTheory.Sequence.IsWeaklyRegular.isQuasiRegularFamily`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open MvPolynomial in
/-- A quasi-regular family (the elementwise form of Stacks 061P, with `J = span (range f)`): if a homogeneous
polynomial `F` of degree `n` satisfies `F(f) ∈ J^{n+1}`, then every coefficient of `F` lies in `J`. Equivalently, the
surjection `(R/J)[X] → gr_J R` is an isomorphism. -/
def IsQuasiRegularFamily {R : Type*} [CommRing R] {ι : Type*} (f : ι → R) : Prop :=
  ∀ (n : ℕ) (F : MvPolynomial ι R), F.IsHomogeneous n →
    MvPolynomial.eval f F ∈ Ideal.span (Set.range f) ^ (n + 1) →
    ∀ m, F.coeff m ∈ Ideal.span (Set.range f)

namespace IsQuasiRegularFamily

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Elements of `J^{n+1}` are values of homogeneous polynomials of degree `n` with coefficients in `J`.
Reference: third sentence of the proof of Stacks 00LN ("any element of J^{n+1} is of the form Σ_{|I|=n} b_I f^I with
b_I ∈ J"). -/
theorem exists_isHomogeneous_coeff_mem_eval_eq {ι : Type*} (f : ι → R) (n : ℕ) {a : R}
    (ha : a ∈ Ideal.span (Set.range f) ^ (n + 1)) :
    ∃ G : MvPolynomial ι R, G.IsHomogeneous n ∧
      (∀ m, G.coeff m ∈ Ideal.span (Set.range f)) ∧ MvPolynomial.eval f G = a := by
  rw [pow_succ'] at ha
  refine Submodule.mul_induction_on ha (fun j hj b hb => ?_) ?_
  · obtain ⟨G, hG, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f b).mp hb
    refine ⟨C j * G, hG.C_mul j, fun m => ?_, by simp⟩
    rw [coeff_C_mul]
    exact Ideal.mul_mem_right _ _ hj
  · rintro a b ⟨G, hG, hGJ, rfl⟩ ⟨G', hG', hGJ', rfl⟩
    exact ⟨G + G', hG.add hG', fun m => by rw [coeff_add]; exact Ideal.add_mem _ (hGJ m) (hGJ' m),
      by simp⟩

/-- **The value at `f` of a homogeneous polynomial of degree `n` with coefficients in `J` lies in `J^{n+1}`.**

Reference: the proof of Stacks 00LN (this is the fact used when rewriting the terms with `a_{I',l} ∈ J'` as terms
of one degree higher); elementary.

Proof: `G = Σ_{m ∈ G.support} monomial m (coeff m G)` (`MvPolynomial.support_sum_monomial_coeff` / `G.as_sum`),
`eval f (monomial m a) = a * eval f (monomial m 1)` (`monomial m a = C a * monomial m 1`:
`MvPolynomial.C_mul_monomial`, `mul_one`). For `m ∈ G.support`, homogeneity gives `m.degree = n` (the definition
of `hG`: `coeff m G ≠ 0 → Finsupp.weight 1 m = n`, `Finsupp.degree_eq_weight_one`; or
`MvPolynomial.isHomogeneous_monomial 1 hdeg`), so `monomial m 1` is homogeneous of degree `n`, and
`Ideal.mem_span_pow_iff_exists_isHomogeneous f _ |>.mpr ⟨monomial m 1, _, rfl⟩` gives
`eval f (monomial m 1) ∈ J^n`. Every term is `∈ J * J^n = J^{n+1}` (`Ideal.mul_mem_mul`, `pow_succ'`), and
`Ideal.sum_mem` concludes.

Edge cases: `n = 0`: `G = C a`, `a ∈ J = J^1`; `ι` empty: as before; `G = 0`. -/
theorem eval_mem_pow_succ_of_coeff_mem {ι : Type*} (f : ι → R) {n : ℕ} {G : MvPolynomial ι R}
    (hG : G.IsHomogeneous n) (hGJ : ∀ m, G.coeff m ∈ Ideal.span (Set.range f)) :
    MvPolynomial.eval f G ∈ Ideal.span (Set.range f) ^ (n + 1) := by
  have hsum : MvPolynomial.eval f G =
      ∑ m ∈ G.support, G.coeff m * MvPolynomial.eval f (monomial m 1) := by
    conv_lhs => rw [G.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [eval_monomial]
  rw [hsum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hdeg : m.degree = n := by
    by_contra hne
    exact (mem_support_iff.mp hm) (hG.coeff_eq_zero hne)
  rw [pow_succ']
  exact Ideal.mul_mem_mul (hGJ m)
    ((Ideal.mem_span_pow_iff_exists_isHomogeneous f _).mpr
      ⟨monomial m 1, isHomogeneous_monomial 1 hdeg, rfl⟩)

/-- **The claim in the proof of Matsumura Thm 16.2**: if `f` is quasi-regular and `x` is a nonzerodivisor modulo
`J = (f)`, then `x` is a nonzerodivisor modulo every `J^ν`.
Induction on `ν`: `x b ∈ J^{ν+1} ⊆ J^ν` ⇒ `b ∈ J^ν`, `b = G(f)` with `G` homogeneous of degree `ν`;
`(xG)(f) ∈ J^{ν+1}` ⇒ (quasi-regularity) `x·coeff ∈ J` ⇒ `coeff ∈ J` ⇒ `b = G(f) ∈ J^{ν+1}`. -/
theorem mem_pow_of_mul_mem_pow {ι : Type*} {f : ι → R} (hQ : IsQuasiRegularFamily f) {x : R}
    (hx : ∀ a, x * a ∈ Ideal.span (Set.range f) → a ∈ Ideal.span (Set.range f)) :
    ∀ (ν : ℕ) (b : R), x * b ∈ Ideal.span (Set.range f) ^ ν → b ∈ Ideal.span (Set.range f) ^ ν := by
  intro ν
  induction ν with
  | zero => intro b _; simp
  | succ ν ih =>
    intro b hb
    have hbν : b ∈ Ideal.span (Set.range f) ^ ν := ih b (Ideal.pow_le_pow_right (Nat.le_succ ν) hb)
    obtain ⟨G, hG, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f b).mp hbν
    refine eval_mem_pow_succ_of_coeff_mem f hG fun m => hx _ ?_
    have := hQ ν (C x * G) (hG.C_mul x) (by simpa using hb) m
    rwa [coeff_C_mul] at this

/-- **Splitting a homogeneous polynomial of degree `n+1` according to whether it involves `X 0`.**

Reference: the proof of Matsumura Thm 16.2(i) ("write F = G(X_1..X_{n−1}) + X_n H"); the expansion
`Σ_e (Σ a_{I',e} f^{I'}) f_c^e` in the proof of Stacks 00LN, split into the parts `e = 0` and `e ≥ 1`.

Statement: `F ∈ R[X_0..X_c]` homogeneous of degree `n+1` ⇒ there are `G ∈ R[X_1..X_c]` (homogeneous of degree
`n+1`) and `H ∈ R[X_0..X_c]` (homogeneous of degree `n`) with `F = rename Fin.succ G + X 0 * H`.

Proof (via `MvPolynomial.finSuccEquiv R c : R[X_0..X_c] ≃ₐ (R[X_1..X_c])[T]`, `X 0 ↦ T`, `X i.succ ↦ C (X i)`):
let `P := finSuccEquiv R c F`, `G := P.coeff 0`, `H := (finSuccEquiv R c).symm P.divX`.
1. `P = Polynomial.C (P.coeff 0) + Polynomial.X * P.divX` (`Polynomial.divX_mul_X_add`, note the order); apply
   `(finSuccEquiv R c).symm` to both sides: `symm (Polynomial.C G) = rename Fin.succ G` (checked on generators via
   `finSuccEquiv_comp_C_eq_C` / `finSuccEquiv_X_succ`, or directly `MvPolynomial.finSuccEquiv_apply` +
   `AlgEquiv.symm_apply_eq`), `symm X = X 0` (`finSuccEquiv_X_zero`).
2. `G` is homogeneous of degree `n+1`: `MvPolynomial.IsHomogeneous.finSuccEquiv_coeff_isHomogeneous hF 0 (n+1) (by simp)`.
3. `H` is homogeneous of degree `n`: by definition — if `coeff m H ≠ 0` then `coeff m H = coeff (m + single 0 1) F`
   (`finSuccEquiv_coeff_coeff` and `Polynomial.coeff_divX`), and `hF` gives `(m + single 0 1).degree = n + 1`,
   so `m.degree = n`.
   Alternatively, without `finSuccEquiv`: `H := Σ_{m ∈ F.support, m 0 ≠ 0} monomial (m - single 0 1) (coeff m F)`,
   `G := Σ_{m ∈ F.support, m 0 = 0} monomial (m.comapDomain Fin.succ _) (coeff m F)`, checked termwise.

Edge case: `c = 0` (only the variable `X 0`): `F = a X_0^{n+1}`, `G = 0` (the only homogeneous polynomial of degree
`n+1 ≥ 1` in zero variables is `0`, which is homogeneous of every degree), `H = a X_0^n`. -/
theorem exists_split_first_variable {c n : ℕ} (F : MvPolynomial (Fin (c + 1)) R)
    (hF : F.IsHomogeneous (n + 1)) :
    ∃ (G : MvPolynomial (Fin c) R) (H : MvPolynomial (Fin (c + 1)) R),
      G.IsHomogeneous (n + 1) ∧ H.IsHomogeneous n ∧
        F = MvPolynomial.rename Fin.succ G + MvPolynomial.X 0 * H := by
  classical
  have hC : ∀ G : MvPolynomial (Fin c) R,
      finSuccEquiv R c (rename Fin.succ G) = Polynomial.C G := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a => simp [finSuccEquiv_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, finSuccEquiv_X_succ]
  refine ⟨(finSuccEquiv R c F).coeff 0, (finSuccEquiv R c).symm (finSuccEquiv R c F).divX,
    hF.finSuccEquiv_coeff_isHomogeneous 0 (n + 1) (by simp), ?_, ?_⟩
  · intro d hd
    have h1 : coeff d ((finSuccEquiv R c).symm (finSuccEquiv R c F).divX) =
        coeff ((Finsupp.tail d).cons (d 0 + 1)) F := by
      rw [← finSuccEquiv_coeff_coeff, ← Polynomial.coeff_divX,
        ← (finSuccEquiv R c).apply_symm_apply (finSuccEquiv R c F).divX, finSuccEquiv_coeff_coeff,
        AlgEquiv.symm_apply_apply, Finsupp.cons_tail]
    rw [h1] at hd
    have h2 := hF hd
    rw [← Finsupp.cons_tail d]
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum_cons] at h2 ⊢
    omega
  · apply (finSuccEquiv R c).injective
    rw [map_add, map_mul, hC, finSuccEquiv_X_zero, AlgEquiv.apply_symm_apply]
    exact ((add_comm _ _).trans (Polynomial.X_mul_divX_add _)).symm

/-- **If `F = rename succ G + X 0 * H` and the coefficients of `G`, `H` lie in the ideal `J`, then the coefficients
of `F` lie in `J`.**

Reference: elementary (last sentence of the proof of Matsumura 16.2(i): "hence all coefficients of F are in I").

Proof: `coeff m F = coeff m (rename Fin.succ G) + coeff m (X 0 * H)` (`coeff_add`).
* Second term: `MvPolynomial.coeff_X_mul'`: `coeff m (X 0 * H) = if 0 ∈ m.support then coeff (m - single 0 1) H else 0`
  `∈ J`.
* First term: `Fin.succ` is injective (`Fin.succ_injective _`). If `m` is of the form `u.mapDomain Fin.succ`,
  `coeff_rename_mapDomain` gives `= coeff u G ∈ J`; otherwise `coeff_rename_eq_zero` gives `0`. (Case split on
  `m ∈ Set.range (Finsupp.mapDomain Fin.succ)`.) -/
theorem coeff_mem_of_split {c : ℕ} {J : Ideal R} {F : MvPolynomial (Fin (c + 1)) R}
    {G : MvPolynomial (Fin c) R} {H : MvPolynomial (Fin (c + 1)) R}
    (hdec : F = MvPolynomial.rename Fin.succ G + MvPolynomial.X 0 * H)
    (hG : ∀ m, G.coeff m ∈ J) (hH : ∀ m, H.coeff m ∈ J) : ∀ m, F.coeff m ∈ J := by
  classical
  intro m
  rw [hdec, coeff_add]
  refine J.add_mem ?_ ?_
  · by_cases hm : ∃ u : Fin c →₀ ℕ, u.mapDomain Fin.succ = m
    · obtain ⟨u, rfl⟩ := hm
      rw [coeff_rename_mapDomain _ (Fin.succ_injective _)]
      exact hG u
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd ⟨u, hu⟩ hm]
      exact J.zero_mem
  · rw [coeff_X_mul']
    split_ifs
    · exact hH _
    · exact J.zero_mem

/-- **The quasi-regularity condition in degree `n = 0` holds automatically for every family.**

Proof: `F` is homogeneous of degree `0`. For `m ≠ 0`, `m.degree ≠ 0` and `hF.coeff_eq_zero` gives
`coeff m F = 0 ∈ J`. For `m = 0`: `F = C (coeff 0 F)` (`MvPolynomial.totalDegree_eq_zero_iff_eq_C`,
`hF.totalDegree_le`; or `homogeneousComponent_zero` + `homogeneousComponent_eq_self`), so `eval f F = coeff 0 F`,
which by hypothesis lies in `J^{0+1} = J` (`pow_one`/`zero_add`). -/
theorem degree_zero {ι : Type*} (f : ι → R) (F : MvPolynomial ι R) (hF : F.IsHomogeneous 0)
    (h : MvPolynomial.eval f F ∈ Ideal.span (Set.range f) ^ (0 + 1)) :
    ∀ m, F.coeff m ∈ Ideal.span (Set.range f) := by
  intro m
  by_cases hm : m = 0
  · subst hm
    have hF' : F = C (F.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hF.totalDegree_le)
    rw [hF', eval_C, zero_add, pow_one] at h
    exact h
  · rw [hF.coeff_eq_zero (fun h0 => hm ((Finsupp.degree_eq_zero_iff m).mp h0))]
    exact Ideal.zero_mem _

/-- **The induction step (Matsumura Thm 16.2(i) / the induction on `c` of Stacks 00LN)**: `Fin.tail f = (f_1..f_c)`
quasi-regular and `f 0` a nonzerodivisor modulo `J' = (f_1..f_c)` ⇒ `f = (f_0, f_1..f_c)` quasi-regular. (Here
`f 0` plays the role of the **last** element `f_c` of the reference.)

Proof (induction on the degree `n`): `n = 0` is `degree_zero`. `n + 1`:
1. By `exists_isHomogeneous_coeff_mem_eval_eq` take `E` with coefficients in `J` and `E(f) = F(f)`; replace `F` by
   `F' := F − E` with `F'(f) = 0`; it suffices that the coefficients of `F'` lie in `J`.
2. `exists_split_first_variable`: `F' = G(X_1..X_c) + X_0 H`. Then `G(f') + f_0 H(f) = 0`, so
   `f_0 · H(f) = −G(f') ∈ J'^{n+1}`.
3. The claim (`mem_pow_of_mul_mem_pow`, using `f'` quasi-regular and `f_0` regular modulo `J'`) ⇒
   `H(f) ∈ J'^{n+1} ⊆ J^{n+1}`; the induction hypothesis on `n` ⇒ the coefficients of `H` lie in `J`.
4. `H(f) ∈ J'^{n+1}` ⇒ `H(f) = h(f')` with `h` homogeneous of degree `n+1`; `(G + f_0 h)(f') = 0 ∈ J'^{n+2}` ⇒
   (`f'` quasi-regular) the coefficients of `G + f_0 h` lie in `J'` ⇒ the coefficients of `G` lie in
   `J' + (f_0) ⊆ J`.
5. Conclude with `coeff_mem_of_split`. -/
theorem of_tail {c : ℕ} (f : Fin (c + 1) → R) (hQ : IsQuasiRegularFamily (Fin.tail f))
    (hreg : ∀ a, f 0 * a ∈ Ideal.span (Set.range (Fin.tail f)) →
      a ∈ Ideal.span (Set.range (Fin.tail f))) :
    IsQuasiRegularFamily f := by
  have hJ'J : Ideal.span (Set.range (Fin.tail f)) ≤ Ideal.span (Set.range f) :=
    Ideal.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, rfl⟩)
  have hf0 : f 0 ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨0, rfl⟩
  intro n
  induction n with
  | zero => exact fun F hF h => degree_zero f F hF h
  | succ n ih =>
    intro F hF h
    obtain ⟨E, hE, hEJ, hEeval⟩ := exists_isHomogeneous_coeff_mem_eval_eq f (n + 1) h
    suffices hsuff : ∀ m, (F - E).coeff m ∈ Ideal.span (Set.range f) by
      intro m
      have h1 := Ideal.add_mem _ (hsuff m) (hEJ m)
      rwa [coeff_sub, sub_add_cancel] at h1
    have h0 : MvPolynomial.eval f (F - E) = 0 := by rw [map_sub, hEeval, sub_self]
    obtain ⟨G, H, hG, hH, hdec⟩ := exists_split_first_variable (F - E) (hF.sub hE)
    have e1 : MvPolynomial.eval (Fin.tail f) G + f 0 * MvPolynomial.eval f H = 0 := by
      rw [hdec, map_add, map_mul, eval_X, eval_rename] at h0
      exact h0
    have hGmem : MvPolynomial.eval (Fin.tail f) G ∈ Ideal.span (Set.range (Fin.tail f)) ^ (n + 1) :=
      (Ideal.mem_span_pow_iff_exists_isHomogeneous _ _).mpr ⟨G, hG, rfl⟩
    have hH1 : MvPolynomial.eval f H ∈ Ideal.span (Set.range (Fin.tail f)) ^ (n + 1) := by
      refine mem_pow_of_mul_mem_pow hQ hreg (n + 1) _ ?_
      rw [eq_neg_of_add_eq_zero_right e1]
      exact neg_mem hGmem
    have hHJ : ∀ m, H.coeff m ∈ Ideal.span (Set.range f) :=
      ih H hH (Ideal.pow_right_mono hJ'J (n + 1) hH1)
    obtain ⟨h', hh', hh'eval⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous _ _).mp hH1
    have hGh : ∀ m, (G + C (f 0) * h').coeff m ∈ Ideal.span (Set.range (Fin.tail f)) := by
      refine hQ (n + 1) _ (hG.add (hh'.C_mul _)) ?_
      rw [map_add, map_mul, eval_C, hh'eval, e1]
      exact Ideal.zero_mem _
    have hGJ : ∀ m, G.coeff m ∈ Ideal.span (Set.range f) := by
      intro m
      have h2 := hGh m
      rw [coeff_add, coeff_C_mul] at h2
      have h3 : G.coeff m = (G.coeff m + f 0 * h'.coeff m) - f 0 * h'.coeff m := by ring
      rw [h3]
      exact Ideal.sub_mem _ (hJ'J h2) (Ideal.mul_mem_right _ _ hf0)
    exact coeff_mem_of_split hdec hGJ hHJ

/-- **The empty family is quasi-regular.**

Proof: `ι` empty, `Set.range f = ∅`, `J = ⊥` (`Set.range_eq_empty`, `Ideal.span_empty`), `J^{n+1} = ⊥`
(`Ideal.bot_pow`, `n + 1 ≠ 0`). For `ι` empty every `m : ι →₀ ℕ` equals `0` (`Subsingleton.elim`),
`F = C (coeff 0 F)` (`MvPolynomial.eq_C_of_isEmpty`), `eval f F = coeff 0 F`. The hypothesis gives
`coeff 0 F = 0`, so `coeff m F = coeff 0 F = 0 ∈ ⊥`. -/
theorem of_isEmpty {ι : Type*} [IsEmpty ι] (f : ι → R) : IsQuasiRegularFamily f := by
  intro n F _ h m
  have hJ : Ideal.span (Set.range f) = ⊥ := by rw [Set.range_eq_empty, Ideal.span_empty]
  rw [hJ, Ideal.bot_pow (Nat.succ_ne_zero n)] at h
  rw [hJ]
  have hF' : F = C (F.coeff 0) := MvPolynomial.eq_C_of_isEmpty F
  have hm : m = 0 := Subsingleton.elim _ _
  subst hm
  rw [hF', eval_C] at h
  exact h

/-- **Quasi-regularity is independent of the ordering of the indices.**

Reference: the sentence after Definition 061P in Stacks 061M: "It is clear that being a quasi-regular sequence is
independent of the order".

Proof: `Set.range (x ∘ e) = Set.range x` (`e.surjective.range_comp`), so both `J`s agree. Given `F ∈ R[ι']`
(homogeneous of degree `n`, `F(x) ∈ J^{n+1}`), let `F' := rename e.symm F ∈ R[ι]`: homogeneous
(`IsHomogeneous.rename_isHomogeneous`), and `eval (x ∘ e) F' = eval (x ∘ e ∘ e.symm) F = eval x F` (`eval_rename`,
`Equiv.self_comp_symm`). By hypothesis the coefficients of `F'` lie in `J`, and
`coeff m F = coeff (m.mapDomain e.symm) F'` (`coeff_rename_mapDomain _ e.symm.injective`). -/
theorem of_comp_equiv {ι ι' : Type*} (e : ι ≃ ι') (x : ι' → R)
    (h : IsQuasiRegularFamily (x ∘ e)) : IsQuasiRegularFamily x := by
  intro n F hF hmem m
  have hr : Set.range (x ∘ e) = Set.range x := e.surjective.range_comp x
  have hev : MvPolynomial.eval (x ∘ e) (rename e.symm F) = MvPolynomial.eval x F := by
    have hc : (x ∘ e) ∘ e.symm = x := by
      ext i
      simp
    rw [eval_rename, hc]
  have h1 := h n (rename e.symm F) hF.rename_isHomogeneous (by rw [hev, hr]; exact hmem)
    (m.mapDomain e.symm)
  rwa [coeff_rename_mapDomain _ e.symm.injective, hr] at h1

end IsQuasiRegularFamily

/-- The image of `Fin.tail f` after `i` = the image of `f` after `i.succ`. -/
theorem Fin.tail_image_Ioi {α : Type*} {c : ℕ} (f : Fin (c + 1) → α) (i : Fin c) :
    Fin.tail f '' Set.Ioi i = f '' Set.Ioi i.succ := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.succ, Fin.succ_lt_succ_iff.mpr hj, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk0 : k ≠ 0 := fun h => by simp [h] at hk
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk0
    exact ⟨j, Fin.succ_lt_succ_iff.mp hk, rfl⟩

/-- The image of `f` after `0` = the range of `Fin.tail f`. -/
theorem Fin.image_Ioi_zero_eq_range_tail {α : Type*} {c : ℕ} (f : Fin (c + 1) → α) :
    f '' Set.Ioi 0 = Set.range (Fin.tail f) := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk0 : k ≠ 0 := fun h => by simp [h] at hk
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk0
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.succ, Fin.succ_pos j, rfl⟩

/-- **The core induction (Stacks 00LN(1), reversed-index form)**: if every `f i` is a nonzerodivisor modulo the
ideal generated by the later elements, then `f` is quasi-regular. -/
theorem isQuasiRegularFamily_of_regular_mod_later {R : Type*} [CommRing R] :
    ∀ (c : ℕ) (f : Fin c → R),
      (∀ i a, f i * a ∈ Ideal.span (f '' Set.Ioi i) → a ∈ Ideal.span (f '' Set.Ioi i)) →
      IsQuasiRegularFamily f := by
  intro c
  induction c with
  | zero => intro f _; exact IsQuasiRegularFamily.of_isEmpty f
  | succ c ih =>
    intro f hf
    refine IsQuasiRegularFamily.of_tail f (ih (Fin.tail f) fun i a => ?_) ?_
    · rw [Fin.tail_image_Ioi]
      exact hf i.succ a
    · rw [← Fin.image_Ioi_zero_eq_range_tail]
      exact hf 0

/-- **`List.ofFn x` weakly regular ⇒ the elementwise form "`x i` is a nonzerodivisor modulo the ideal generated by the
preceding elements".**

Reference: the translation between the definition of a regular sequence (Stacks 00LF) and Mathlib's
`RingTheory.Sequence.IsWeaklyRegular`.

Proof: `RingTheory.Sequence.isWeaklyRegular_iff_Fin`: for every `j : Fin (List.ofFn x).length`,
`IsSMulRegular (R ⧸ (Ideal.ofList ((List.ofFn x).take j) • ⊤ : Submodule R R)) (List.ofFn x)[j]`.
Take `j = i.cast (List.length_ofFn).symm`: `(List.ofFn x)[j] = x i` (`List.getElem_ofFn`).
`isSMulRegular_quotient_iff_mem_of_smul_mem` (`IsSMulRegular (M ⧸ N) r ↔ ∀ m, r • m ∈ N → m ∈ N`) turns this
into the elementwise form; `I • (⊤ : Submodule R R) = I` (`smul_eq_mul`, `Ideal.mul_top`). Finally
`Ideal.ofList ((List.ofFn x).take i) = Ideal.span (x '' Set.Iio i)`: `Ideal.ofList l = span {r | r ∈ l}` and
`r ∈ (List.ofFn x).take i ↔ ∃ k < i, x k = r` (`List.mem_take_iff_getElem` + `List.getElem_ofFn`). -/
theorem RingTheory.Sequence.IsWeaklyRegular.elementwise_of_ofFn {R : Type*} [CommRing R] {c : ℕ}
    {x : Fin c → R} (h : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    ∀ i a, x i * a ∈ Ideal.span (x '' Set.Iio i) → a ∈ Ideal.span (x '' Set.Iio i) := by
  intro i a ha
  have hlen : (i : ℕ) < (List.ofFn x).length := by simp
  have hreg := h.regular_mod_prev i hlen
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hreg
  have hI : (Ideal.ofList ((List.ofFn x).take i) • (⊤ : Submodule R R)) =
      Ideal.span (x '' Set.Iio i) := by
    rw [smul_eq_mul, Ideal.mul_top]
    unfold Ideal.ofList
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq, List.mem_take_iff_getElem, List.getElem_ofFn, Set.mem_image,
      Set.mem_Iio]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hkc : k < c := by
        have := hk; simp only [List.length_ofFn] at this; omega
      exact ⟨⟨k, hkc⟩, by
        have := hk; simp only [List.length_ofFn] at this
        exact Fin.lt_def.mpr (by simp; omega), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, by simp only [List.length_ofFn]; have := Fin.lt_def.mp hk; omega, rfl⟩
  rw [hI] at hreg
  have hget : (List.ofFn x)[(i : ℕ)] = x i := by simp
  rw [hget] at hreg
  exact hreg a (by simpa [smul_eq_mul] using ha)

/-- The image of `x ∘ Fin.rev` after `i` = the image of `x` before `Fin.rev i`. -/
theorem Fin.comp_rev_image_Ioi {α : Type*} {c : ℕ} (x : Fin c → α) (i : Fin c) :
    (x ∘ Fin.rev) '' Set.Ioi i = x '' Set.Iio (Fin.rev i) := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.rev j, Fin.rev_lt_rev.mpr hj, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨Fin.rev k, ?_, by simp⟩
    have : Fin.rev (Fin.rev i) < Fin.rev k := Fin.rev_lt_rev.mpr hk
    simpa using this

/-- **Stacks 00LN(1): a regular sequence is quasi-regular** (any commutative ring; no Noetherian, local, or
`R/J ≠ 0` hypothesis). -/
theorem RingTheory.Sequence.IsWeaklyRegular.isQuasiRegularFamily {R : Type*} [CommRing R] {c : ℕ}
    {x : Fin c → R} (h : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    IsQuasiRegularFamily x := by
  have hel := h.elementwise_of_ofFn
  refine IsQuasiRegularFamily.of_comp_equiv Fin.revPerm x ?_
  refine isQuasiRegularFamily_of_regular_mod_later c (x ∘ Fin.revPerm) fun i a => ?_
  have : (x ∘ (Fin.revPerm : Fin c → Fin c)) = x ∘ Fin.rev := rfl
  rw [this, Fin.comp_rev_image_Ioi]
  exact hel (Fin.rev i) a

end
