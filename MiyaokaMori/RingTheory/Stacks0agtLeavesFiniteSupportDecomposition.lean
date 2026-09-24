import MiyaokaMori.Prelude
import Mathlib.RingTheory.Support

/-! # A finitely supported module is the product of its localizations

A finitely generated module over a Noetherian ring whose support consists of finitely many
**maximal** ideals is the product of its localizations at those maximal ideals.

This is the algebraic content of "a coherent sheaf supported at finitely many closed points is
the direct sum of its stalks (a sum of skyscrapers)", used in Stacks 0AGT (step 2 of the length
inequality).

Sources: Stacks 00JA (Artinian rings are products of local Artinian rings), Atiyah–Macdonald
Thm 8.7; for modules: Eisenbud, *Commutative Algebra*, Cor. 2.16 (a finite-length module is the
direct sum of its localizations at maximal ideals).

The proof is elementwise and avoids the Artinian quotient / module Chinese remainder theorem: it
only uses `(∏_{q ∈ S} q)^n ⊆ Ann(G)` (support = `V(Ann G)` for finite modules, plus
`Ideal.exists_pow_le_of_le_radical_of_fg`) and comaximality of `p^n` and `∏_{q ≠ p} q^n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

/-- **Finite-support modules are products of their localizations.** `B` Noetherian, `G` a finitely
generated `B`-module, `S` a finite set of maximal ideals containing the support of `G`. Then
`G → Π_{𝔪 ∈ S} G_𝔪`, `g ↦ (g/1)_𝔪`, is bijective.

Proof (as formalized; elementwise version of Eisenbud Cor. 2.16 / Atiyah–Macdonald 8.7):
0. **A uniform power killing `G`.** Since `G` is finitely generated, `supp G = V(Ann G)`
   (`Module.support_eq_zeroLocus`), so every prime containing `𝔞 := Ann_B(G)` lies in `S`; hence
   `⨅_{q ∈ S} q ≤ rad 𝔞` (`Ideal.radical_eq_sInf`), and as `B` is Noetherian some power
   `(⨅_{q∈S} q)^k ≤ 𝔞` (`Ideal.exists_pow_le_of_le_radical_of_fg`). With `n := k + 1 ≥ 1` this
   gives `∏_{q ∈ S} q^n ≤ 𝔞` (`Ideal.prod_le_inf`, `Finset.prod_pow`).
1. **The elements `e_p`.** For `p ∈ S`, the ideals `p^n` and `∏_{q ∈ S ∖ {p}} q^n` are comaximal
   (`Ideal.IsMaximal.coprime_of_ne`, `IsCoprime.pow`, `IsCoprime.prod_right`), so there is
   `e_p ∈ ∏_{q ≠ p} q^n` with `1 - e_p ∈ p^n`. Then `x · e_p ∈ ∏_{q∈S} q^n ⊆ 𝔞` for every
   `x ∈ p^n`, i.e. `(x e_p) • g = 0` for all `g`. Moreover `e_p ∉ p` (else `1 ∈ p`) and, for
   `q ∈ S`, `q ≠ p`: `e_p ∈ q` and hence `1 - e_p ∉ q`.
   * (A) For `q ≠ p`: `(e_p • g)/1 = 0` in `G_q`, witnessed by `1 - e_p ∉ q` and
     `((1 - e_p) e_p) • g = 0`.
   * (B) `(e_p • g)/1 = g/1` in `G_p`, witnessed by `e_p ∉ p` and `((e_p - 1) e_p) • g = 0`.
   * (C) For `s ∉ p` and `g ∈ G` there is `t ∈ B` with `g/s = (t • g)/1` in `G_p`: `(s)` and `p`
     are comaximal (`Ideal.IsMaximal.exists_inv`), hence so are `(s)` and `p^n`, giving
     `1 - t s ∈ p^n`; the witness is again `e_p ∉ p`, since `((1 - t s) e_p) • g = 0`.
2. **Injectivity.** Let `g ↦ 0`; suppose `g ≠ 0`. Then `Ann(g) ≠ ⊤`, so `Ann(g) ≤ 𝔪` for some
   maximal `𝔪` (`Ideal.exists_le_maximal`); by `Module.mem_support_iff_exists_annihilator`,
   `𝔪 ∈ supp G ⊆ S`, so `g/1 = 0` in `G_𝔪`, i.e. `u • g = 0` for some `u ∉ 𝔪`
   (`LocalizedModule.mk_eq`) — but then `u ∈ Ann(g) ≤ 𝔪`, contradiction. (No power `n` needed.)
3. **Surjectivity.** Given `(x_p)_{p ∈ S}`, write `x_p = g_p / s_p` and choose `t_p` as in (C).
   Put `g := ∑_{p ∈ S} e_p • (t_p • g_p)`. In `G_q` all summands with `p ≠ q` vanish by (A), and the
   `q`-summand equals `(t_q • g_q)/1 = g_q / s_q = x_q` by (B) and (C). -/
theorem Module.bijective_pi_localizedModule_of_support_subset {B : Type u} [CommRing B]
    [IsNoetherianRing B] (G : Type u) [AddCommGroup G] [Module B G] [Module.Finite B G]
    (S : Finset (PrimeSpectrum B)) (hS : ∀ p ∈ S, p.asIdeal.IsMaximal)
    (hsupp : Module.support B G ⊆ ↑S) :
    Function.Bijective
      (fun g : G => fun p : S => LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl G g) := by
  classical
  -- Step 0: a uniform power `n ≥ 1` with `(∏_{q ∈ S} q^n) • G = 0`.
  have hJ : S.inf (fun q => q.asIdeal) ≤ (Module.annihilator B G).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hJ1, hJ2⟩
    have hmem : (⟨J, hJ2⟩ : PrimeSpectrum B) ∈ S := by
      apply hsupp
      rw [Module.support_eq_zeroLocus]
      exact hJ1
    exact Finset.inf_le hmem
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ (IsNoetherian.noetherian _)
  set n := k + 1 with hn
  have hn0 : n ≠ 0 := Nat.succ_ne_zero k
  have hP : ∏ q ∈ S, q.asIdeal ^ n ≤ Module.annihilator B G := by
    rw [Finset.prod_pow]
    exact (Ideal.pow_right_mono Ideal.prod_le_inf n).trans
      ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)
  have hP' : ∀ x ∈ ∏ q ∈ S, q.asIdeal ^ n, ∀ g : G, x • g = 0 := fun x hx g =>
    Module.mem_annihilator.mp (hP hx) g
  -- Step 1: for `p ∈ S`, an element `e p ∈ ∏_{q ∈ S, q ≠ p} q^n` with `1 - e p ∈ p^n`.
  have hcop : ∀ p ∈ S, IsCoprime (p.asIdeal ^ n) (∏ q ∈ S.erase p, q.asIdeal ^ n) := by
    intro p hp
    refine IsCoprime.prod_right fun q hq => ?_
    have hne : p.asIdeal ≠ q.asIdeal := fun h =>
      (Finset.ne_of_mem_erase hq) (PrimeSpectrum.ext h).symm
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      ((hS p hp).coprime_of_ne (hS q (Finset.mem_of_mem_erase hq)) hne)).pow
  have he : ∀ p ∈ S, ∃ e : B, e ∈ ∏ q ∈ S.erase p, q.asIdeal ^ n ∧ (1 - e) ∈ p.asIdeal ^ n := by
    intro p hp
    obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp (hcop p hp)
    exact ⟨j, hj, by rw [← hij]; simpa using hi⟩
  choose! e he1 he2 using he
  -- `x * e p` kills `G` for every `x ∈ p^n`.
  have hkill : ∀ p ∈ S, ∀ x ∈ p.asIdeal ^ n, ∀ g : G, (x * e p) • g = 0 := by
    intro p hp x hx g
    apply hP'
    rw [← Finset.mul_prod_erase S _ hp]
    exact Ideal.mul_mem_mul hx (he1 p hp)
  have he_notMem : ∀ p ∈ S, e p ∉ p.asIdeal := by
    intro p hp h
    have h1 : (1 : B) ∈ p.asIdeal := by
      have := Ideal.pow_le_self hn0 (he2 p hp)
      simpa using p.asIdeal.add_mem this h
    exact (hS p hp).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have he_mem : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → e p ∈ q.asIdeal := by
    intro p hp q hq hpq
    have hq' : q ∈ S.erase p := Finset.mem_erase.mpr ⟨fun h => hpq h.symm, hq⟩
    exact Ideal.pow_le_self hn0 ((Ideal.prod_le_inf.trans (Finset.inf_le hq')) (he1 p hp))
  -- Claim A: `e p • g ↦ 0` in `G_q` for `q ≠ p`.
  have hA : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ g : G,
      LocalizedModule.mk (e p • g) (1 : q.asIdeal.primeCompl) = 0 := by
    intro p hp q hq hpq g
    rw [← LocalizedModule.zero_mk (1 : q.asIdeal.primeCompl), LocalizedModule.mk_eq]
    have h1 : (1 - e p) ∈ q.asIdeal.primeCompl := by
      intro h
      have : (1 : B) ∈ q.asIdeal := by simpa using q.asIdeal.add_mem h (he_mem p hp q hq hpq)
      exact (hS q hq).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    refine ⟨⟨1 - e p, h1⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul, smul_zero, ← mul_smul]
    exact hkill p hp _ (he2 p hp) g
  -- Claim B: `e p • g ↦ g` in `G_p`.
  have hB : ∀ p ∈ S, ∀ g : G,
      LocalizedModule.mk (e p • g) (1 : p.asIdeal.primeCompl) = LocalizedModule.mk g 1 := by
    intro p hp g
    rw [LocalizedModule.mk_eq]
    refine ⟨⟨e p, he_notMem p hp⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul, ← mul_smul]
    have h := hkill p hp (e p - 1) (by rw [← neg_sub]; exact neg_mem (he2 p hp)) g
    rw [sub_mul, one_mul, sub_smul, sub_eq_zero] at h
    exact h
  -- Claim C: every `g / s ∈ G_p` is of the form `(t • g) / 1`.
  have hC : ∀ p ∈ S, ∀ (s : p.asIdeal.primeCompl) (g : G), ∃ t : B,
      LocalizedModule.mk g s = LocalizedModule.mk (t • g) (1 : p.asIdeal.primeCompl) := by
    intro p hp s g
    obtain ⟨y, i, hi, hyi⟩ := (hS p hp).exists_inv s.2
    have hcop' : IsCoprime (Ideal.span {(s : B)}) (p.asIdeal ^ n) :=
      (Ideal.isCoprime_iff_exists.mpr
        ⟨y * s, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), i, hi, hyi⟩).pow_right
    obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp hcop'
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨t, ?_⟩
    rw [LocalizedModule.mk_eq]
    refine ⟨⟨e p, he_notMem p hp⟩, ?_⟩
    have hb' : (1 - t * s) ∈ p.asIdeal ^ n := by rw [← hab]; simpa using hb
    have h := hkill p hp _ hb' g
    rw [sub_mul, one_mul, sub_smul, sub_eq_zero] at h
    simp only [Submonoid.smul_def, one_smul, ← mul_smul]
    rw [h]
    congr 1
    ring
  refine ⟨fun g₁ g₂ h => ?_, fun x => ?_⟩
  · -- Injectivity.
    rw [← sub_eq_zero]
    have hg : ∀ p : S, LocalizedModule.mk (g₁ - g₂) (1 : p.1.asIdeal.primeCompl) = 0 := by
      intro p
      have := congrFun h p
      simp only [LocalizedModule.mkLinearMap_apply] at this
      rw [← LocalizedModule.mkLinearMap_apply, ← LocalizedModule.mkLinearMap_apply,
        ← sub_eq_zero, ← map_sub, LocalizedModule.mkLinearMap_apply] at this
      exact this
    by_contra hne
    have hAnn : (Submodule.span B {g₁ - g₂}).annihilator ≠ ⊤ := by
      intro htop
      have : (1 : B) ∈ (Submodule.span B {g₁ - g₂}).annihilator := htop ▸ Submodule.mem_top
      rw [Submodule.mem_annihilator_span_singleton, one_smul] at this
      exact hne this
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hAnn
    have hmS : (⟨m, hm.isPrime⟩ : PrimeSpectrum B) ∈ S :=
      hsupp (Module.mem_support_iff_exists_annihilator.mpr ⟨g₁ - g₂, hle⟩)
    have h0 := hg ⟨⟨m, hm.isPrime⟩, hmS⟩
    rw [← LocalizedModule.zero_mk (1 : m.primeCompl), LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    simp only [Submonoid.smul_def, one_smul, smul_zero] at hu
    exact u.2 (hle ((Submodule.mem_annihilator_span_singleton _ _).mpr hu))
  · -- Surjectivity.
    have hrep : ∀ p : S, ∃ (g : G) (s : p.1.asIdeal.primeCompl), LocalizedModule.mk g s = x p :=
      fun p => LocalizedModule.induction_on
        (β := fun y => ∃ (g : G) (s : p.1.asIdeal.primeCompl), LocalizedModule.mk g s = y)
        (fun g s => ⟨g, s, rfl⟩) (x p)
    choose gg ss hgs using hrep
    have ht : ∀ p : S, ∃ t : B, LocalizedModule.mk (gg p) (ss p) =
        LocalizedModule.mk (t • gg p) (1 : p.1.asIdeal.primeCompl) :=
      fun p => hC p.1 p.2 (ss p) (gg p)
    choose t ht using ht
    refine ⟨∑ p : S, e p.1 • (t p • gg p), ?_⟩
    funext q
    simp only [map_sum, LocalizedModule.mkLinearMap_apply]
    rw [Finset.sum_eq_single q]
    · rw [hB q.1 q.2, ← ht q, hgs q]
    · intro p _ hpq
      exact hA p.1 p.2 q.1 q.2 (fun h => hpq (Subtype.ext h)) _
    · intro h
      exact absurd (Finset.mem_univ q) h

end
