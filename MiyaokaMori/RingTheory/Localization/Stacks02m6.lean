import MiyaokaMori.Prelude
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Module

/-! # Removing embedded primes (Stacks 02M6, 02M7)

Stacks 02M6/02M7: `R` Noetherian, `M` finite; the submodule `K` of elements that localize to `0` at every
minimal point of `Supp M` (`Module.embeddedPart`) is the largest submodule whose support is nowhere dense
in `Supp M`; `M/K` has the same support as `M` and no embedded associated primes; if `f` lies in all embedded
associated primes then `M_f ≅ (M/K)_f`; and the construction commutes with localization, `K(M)_f = K(M_f)`.
Also the definition `Module.HasNoEmbeddedPrimes` ("a module has no embedded associated primes").

References: Stacks 02M6 (algebra-lemma-remove-embedded-primes), 02M7
(algebra-lemma-remove-embedded-primes-localize), 02M5 (definition).

## Proof outline

Write `K := Module.embeddedPart R M = ⋂_q ker (M → M_q)`, `q` running over the minimal points of
`Supp M`. Membership is elementwise: `m ∈ K ↔ ∀ q minimal, ∃ r ∉ q, r • m = 0`
(`Module.mem_embeddedPart_iff`).

* Minimal points of `Supp M = V(Ann M)` are the minimal primes over `Ann M`
  (`Module.minimal_support_iff`); hence they are finitely many (`R` Noetherian,
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`), every point of `Supp M` lies over one
  (`Ideal.exists_minimalPrimes_le`), and they are associated primes
  (`Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`, Stacks 02CE).
* `Supp K` is nowhere dense in `Supp M`: `Supp K` is closed (`K` is finite over the Noetherian `R`)
  and contains no minimal point `q` (elements of `K` die in `M_q`, so `K_q = 0`); a closed subset
  of `Supp M` missing every generic point has empty interior
  (`PrimeSpectrum.isNowhereDense_preimage_of_forall_exists_le`).
* Maximality: if `Supp K'` is nowhere dense and `q ∈ Supp K'` for a minimal `q`, then
  `V(q) ∖ ⋃_{q' ≠ q} V(q')` is a nonempty open subset of `Supp M` inside `Supp K'`, contradiction;
  so `K'_q = 0` for all minimal `q`, i.e. `K' ≤ K` (`Module.le_embeddedPart_of_isNowhereDense`).
* `Supp (M/K) = Supp M`: `⊆` since `M → M/K` is onto; `⊇` since for a minimal `q`, `M_q → (M/K)_q`
  is injective (`K_q = 0`) and `Supp (M/K)` is stable under specialization.
* `M/K` has no embedded primes: an associated prime `p = Ann(m̄)` of `M/K` (Noetherian: no radical
  needed, `isAssociatedPrime_iff`) satisfies `p ≤ q` for the minimal `q` with `m/1 ≠ 0` in `M_q`,
  and `p ∈ Supp M` lies over some minimal `q'`, so `q' ≤ p ≤ q` forces `p = q`. Thus
  `Ass (M/K) ⊆ {minimal points}`, which are pairwise incomparable.
* `M_f ≅ (M/K)_f` when `f` lies in all embedded primes: for `k ∈ K`, each minimal prime `P` over
  `Ann(k)` is an associated prime of `R k ⊆ M` that is not a minimal point of `Supp M`, hence
  embedded, so `f ∈ P`; therefore `f ∈ √Ann(k)`, `f^n k = 0`, and `K_f = 0`
  (`Module.exists_pow_smul_eq_zero_of_mem_embeddedPart`).
* 02M7 (`K(M)_f = K(M_f)`): primes of `R_f` correspond to primes `q ∌ f` of `R`, compatibly with
  supports and minimality (`Module.minimal_support_localizedModule_away_iff`, via the topological
  embedding `Spec R_f → Spec R`). Then `m/s ∈ K(M_f) ↔ ∀ q minimal with f ∉ q, ∃ r ∉ q, r m = 0`,
  and `m/s ∈ K(M)_f ↔ ∃ n, f^n m ∈ K(M)`; the two agree because for the (finitely many) minimal
  `q ∋ f` one has `r f^n ∈ Ann M` for some `r ∉ q` (`Module.embeddedPart.exists_mul_pow_mem_of_mem_minimalPrimes`,
  from `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- A module has no embedded associated primes: no strict inclusion between associated primes (Stacks 02M5:
   embedded associated primes = non-minimal associated primes). -/

def Module.HasNoEmbeddedPrimes (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ p ∈ associatedPrimes R M, ∀ q ∈ associatedPrimes R M, p ≤ q → p = q

/- The submodule `K` of Stacks 02M6: the elements localizing to `0` at every minimal point `q` of `Supp M`
   (= the `{m | Supp(Rm) ⊆ ⋃ V(p_i)}` of the proof of 02M6, `p_i` the embedded associated primes; for
   Noetherian `R` and finite `M` the two agree). -/

noncomputable def Module.embeddedPart (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Submodule R M :=
  ⨅ (q : PrimeSpectrum R) (_ : Minimal (· ∈ Module.support R M) q),
    LinearMap.ker (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)

section Basic

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

theorem Module.mem_embeddedPart_iff (m : M) :
    m ∈ Module.embeddedPart R M ↔
      ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q →
        ∃ r ∉ q.asIdeal, r • m = 0 := by
  simp only [Module.embeddedPart, Submodule.mem_iInf, LocalizedModule.mem_ker_mkLinearMap_iff]
  rfl

theorem Module.minimal_support_iff [Module.Finite R M] (q : PrimeSpectrum R) :
    Minimal (· ∈ Module.support R M) q ↔
      q.asIdeal ∈ (Module.annihilator R M).minimalPrimes := by
  constructor
  · rintro ⟨hq, hmin⟩
    refine ⟨⟨q.isPrime, Module.mem_support_iff_of_finite.mp hq⟩, ?_⟩
    rintro J ⟨hJ, hIJ⟩ hJq
    exact hmin (y := ⟨J, hJ⟩) (Module.mem_support_iff_of_finite.mpr hIJ) hJq
  · rintro ⟨⟨hq, hIq⟩, hmin⟩
    refine ⟨Module.mem_support_iff_of_finite.mpr hIq, ?_⟩
    intro y hy hyq
    exact hmin ⟨y.isPrime, Module.mem_support_iff_of_finite.mp hy⟩ hyq

theorem Module.finite_setOf_minimal_support [IsNoetherianRing R] [Module.Finite R M] :
    {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q}.Finite := by
  have h := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Module.annihilator R M)
  refine (h.preimage (f := PrimeSpectrum.asIdeal) (fun x _ y _ hxy ↦ PrimeSpectrum.ext hxy)).subset ?_
  intro q hq
  exact (Module.minimal_support_iff q).mp hq

theorem Module.exists_minimal_support_le [Module.Finite R M] {p : PrimeSpectrum R}
    (hp : p ∈ Module.support R M) :
    ∃ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q ∧ q ≤ p := by
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hp)
  exact ⟨⟨q, hq.isPrime⟩, (Module.minimal_support_iff _).mpr hq, hqp⟩

theorem Module.minimal_support_mem_associatedPrimes [IsNoetherianRing R] [Module.Finite R M]
    {q : PrimeSpectrum R} (hq : Minimal (· ∈ Module.support R M) q) :
    q.asIdeal ∈ associatedPrimes R M :=
  Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
    ((Module.minimal_support_iff q).mp hq)

theorem Module.mem_support_of_isAssociatedPrime {p : Ideal R} (hp : IsAssociatedPrime p M) :
    (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  obtain ⟨hprime, x, hx⟩ := hp
  rw [Module.mem_support_iff_exists_annihilator]
  refine ⟨x, fun r hr ↦ ?_⟩
  rw [Submodule.mem_annihilator_span_singleton] at hr
  show r ∈ p
  rw [hx]
  exact Ideal.le_radical (Submodule.mem_colon_singleton.mpr (by simpa using hr))

end Basic

section Topology

variable {R : Type u} [CommRing R]

/-- Auxiliary: a closed subset `S ⊆ T` of `Spec R` containing no "generic point" of `T`
(every point of `T` is a specialization of a point of `T \ S`) is nowhere dense in `T`. -/
theorem PrimeSpectrum.isNowhereDense_preimage_of_forall_exists_le {T S : Set (PrimeSpectrum R)}
    (hS : IsClosed S) (hgen : ∀ x ∈ T, ∃ q ∈ T, q ≤ x ∧ q ∉ S) :
    IsNowhereDense (Subtype.val ⁻¹' S : Set ↥T) := by
  have hcl : IsClosed (Subtype.val ⁻¹' S : Set ↥T) := hS.preimage continuous_subtype_val
  rw [hcl.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
  rintro ⟨x, hxT⟩ hx
  rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hx
  obtain ⟨t, ht, hts⟩ := hx
  obtain ⟨q, hqT, hqx, hqS⟩ := hgen x hxT
  have hxq : x ∈ closure ({q} : Set (PrimeSpectrum R)) := (PrimeSpectrum.le_iff_mem_closure q x).mp hqx
  obtain ⟨y, hyt, hyq⟩ := mem_closure_iff_nhds.mp hxq t ht
  rw [Set.mem_singleton_iff] at hyq
  have hqt : (⟨q, hqT⟩ : ↥T) ∈ Subtype.val ⁻¹' t := by
    show q ∈ t
    rw [← hyq]
    exact hyt
  exact hqS (hts hqt)

end Topology

section Main

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

theorem Module.notMem_support_embeddedPart_of_minimal {q : PrimeSpectrum R}
    (hq : Minimal (· ∈ Module.support R M) q) :
    q ∉ Module.support R ↥(Module.embeddedPart R M) := by
  rw [Module.notMem_support_iff']
  intro k
  obtain ⟨r, hr, hrk⟩ := (Module.mem_embeddedPart_iff (k : M)).mp k.2 q hq
  exact ⟨r, hr, Subtype.ext (by simpa using hrk)⟩

theorem Module.embeddedPart_isNowhereDense_support [IsNoetherianRing R] [Module.Finite R M] :
    IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥(Module.embeddedPart R M) :
      Set ↥(Module.support R M)) := by
  refine PrimeSpectrum.isNowhereDense_preimage_of_forall_exists_le Module.isClosed_support ?_
  intro x hx
  obtain ⟨q, hq, hqx⟩ := Module.exists_minimal_support_le hx
  exact ⟨q, hq.prop, hqx, Module.notMem_support_embeddedPart_of_minimal hq⟩

theorem Module.le_embeddedPart_of_isNowhereDense [IsNoetherianRing R] [Module.Finite R M]
    (K' : Submodule R M)
    (hK' : IsNowhereDense (Subtype.val ⁻¹' Module.support R ↥K' : Set ↥(Module.support R M))) :
    K' ≤ Module.embeddedPart R M := by
  intro k hk
  rw [Module.mem_embeddedPart_iff]
  intro q hq
  by_cases hqS : q ∈ Module.support R ↥K'
  · exfalso
    have hS' : IsClosed (Module.support R ↥K') := Module.isClosed_support
    have hfin := Module.finite_setOf_minimal_support (R := R) (M := M)
    -- the closed set `C` of the other irreducible components
    set C : Set (PrimeSpectrum R) :=
      ⋃ q' ∈ {q' : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q'} \ {q},
        closure ({q'} : Set (PrimeSpectrum R)) with hC
    have hCcl : IsClosed C :=
      hfin.sdiff.isClosed_biUnion (fun _ _ ↦ isClosed_closure)
    have hqC : q ∉ C := by
      intro hqC
      rw [hC, Set.mem_iUnion₂] at hqC
      obtain ⟨q', ⟨hq', hq'q⟩, hqq'⟩ := hqC
      have hle : q' ≤ q := (PrimeSpectrum.le_iff_mem_closure q' q).mpr hqq'
      exact hq'q (le_antisymm hle (hq.2 hq'.1 hle))
    have hsub : (Subtype.val ⁻¹' Cᶜ : Set ↥(Module.support R M)) ⊆
        Subtype.val ⁻¹' Module.support R ↥K' := by
      rintro ⟨x, hxT⟩ hxC
      obtain ⟨q', hq', hq'x⟩ := Module.exists_minimal_support_le hxT
      have hq'q : q' = q := by
        by_contra hne
        apply hxC
        rw [hC, Set.mem_iUnion₂]
        exact ⟨q', ⟨hq', hne⟩, (PrimeSpectrum.le_iff_mem_closure q' x).mp hq'x⟩
      subst hq'q
      exact closure_minimal (Set.singleton_subset_iff.mpr hqS) hS'
        ((PrimeSpectrum.le_iff_mem_closure q' x).mp hq'x)
    have hopen : IsOpen (Subtype.val ⁻¹' Cᶜ : Set ↥(Module.support R M)) :=
      hCcl.isOpen_compl.preimage continuous_subtype_val
    have hmem : (⟨q, hq.prop⟩ : ↥(Module.support R M)) ∈
        interior (closure (Subtype.val ⁻¹' Module.support R ↥K' : Set ↥(Module.support R M))) :=
      interior_maximal (hsub.trans subset_closure) hopen hqC
    rw [hK'] at hmem
    exact hmem
  · obtain ⟨r, hr, hrk⟩ := Module.notMem_support_iff'.mp hqS ⟨k, hk⟩
    exact ⟨r, hr, by simpa using congrArg Subtype.val hrk⟩

theorem Module.support_quotient_embeddedPart [Module.Finite R M] :
    Module.support R (M ⧸ Module.embeddedPart R M) = Module.support R M := by
  apply le_antisymm (Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _))
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Module.exists_minimal_support_le hp
  refine Module.mem_support_mono hqp ?_
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hq.prop
  rw [Module.mem_support_iff']
  refine ⟨Submodule.Quotient.mk m, fun r hr hrm ↦ ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Module.mem_embeddedPart_iff] at hrm
  obtain ⟨r', hr', hr'rm⟩ := hrm q hq
  exact hm (r' * r) (fun h ↦ (q.isPrime.mem_or_mem h).elim hr' hr) (by rw [mul_smul]; exact hr'rm)

theorem Module.minimal_of_mem_associatedPrimes_quotient_embeddedPart [IsNoetherianRing R]
    [Module.Finite R M] {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ Module.embeddedPart R M)) :
    Minimal (· ∈ Module.support R M) (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := by
  have hpS : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M := by
    rw [← Module.support_quotient_embeddedPart]
    exact Module.mem_support_of_isAssociatedPrime hp
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hmK : m ∉ Module.embeddedPart R M := by
    intro h
    apply hprime.ne_top
    rw [Ideal.eq_top_iff_one, hx, Submodule.mem_colon_singleton, one_smul, Submodule.mem_bot,
      Submodule.Quotient.mk_eq_zero]
    exact h
  rw [Module.mem_embeddedPart_iff] at hmK
  push Not at hmK
  obtain ⟨q, hq, hqm⟩ := hmK
  have hpq : p ≤ q.asIdeal := by
    intro r hr
    by_contra hrq
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Module.mem_embeddedPart_iff] at hr
    obtain ⟨r', hr', hr'rm⟩ := hr q hq
    exact hqm (r' * r) (fun h ↦ (q.isPrime.mem_or_mem h).elim hr' hrq)
      (by rw [mul_smul]; exact hr'rm)
  obtain ⟨q', hq', hq'p⟩ := Module.exists_minimal_support_le hpS
  have hq'q : q' ≤ q := hq'p.trans hpq
  have hqq' : q = q' := le_antisymm (hq.2 hq'.1 hq'q) hq'q
  subst hqq'
  have hpq' : (⟨p, hprime⟩ : PrimeSpectrum R) = q := le_antisymm hpq hq'p
  rw [hpq']
  exact hq

theorem Module.hasNoEmbeddedPrimes_quotient_embeddedPart [IsNoetherianRing R] [Module.Finite R M] :
    Module.HasNoEmbeddedPrimes R (M ⧸ Module.embeddedPart R M) := by
  intro p hp q hq hpq
  have hp' := Module.minimal_of_mem_associatedPrimes_quotient_embeddedPart hp
  have hq' := Module.minimal_of_mem_associatedPrimes_quotient_embeddedPart hq
  have := hq'.eq_of_le hp'.prop hpq
  exact congrArg PrimeSpectrum.asIdeal this

theorem Module.exists_pow_smul_eq_zero_of_mem_embeddedPart [IsNoetherianRing R] [Module.Finite R M]
    {f : R} (hf : ∀ p ∈ associatedPrimes R M, (∃ q ∈ associatedPrimes R M, q < p) → f ∈ p)
    {k : M} (hk : k ∈ Module.embeddedPart R M) : ∃ n : ℕ, f ^ n • k = 0 := by
  have hrad : f ∈ (R ∙ k).annihilator.radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    have hPprime : P.IsPrime := hP.isPrime
    have hPass : P ∈ associatedPrimes R M :=
      associatedPrimes.subset_of_injective (f := (R ∙ k).subtype) Subtype.val_injective
        (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ hP)
    have hPnotmin : ¬ Minimal (· ∈ Module.support R M) (⟨P, hPprime⟩ : PrimeSpectrum R) := by
      intro hmin
      obtain ⟨r, hr, hrk⟩ := (Module.mem_embeddedPart_iff k).mp hk _ hmin
      exact hr (hP.le ((Submodule.mem_annihilator_span_singleton k r).mpr hrk))
    obtain ⟨q, hq, hqP⟩ :=
      Module.exists_minimal_support_le (Module.mem_support_of_isAssociatedPrime hPass)
    refine hf P hPass ⟨q.asIdeal, Module.minimal_support_mem_associatedPrimes hq,
      lt_of_le_of_ne hqP ?_⟩
    intro hqP'
    apply hPnotmin
    have : q = ⟨P, hPprime⟩ := PrimeSpectrum.ext hqP'
    exact this ▸ hq
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  exact ⟨n, (Submodule.mem_annihilator_span_singleton k (f ^ n)).mp hn⟩

theorem Module.bijective_localizedMap_mkQ_embeddedPart [IsNoetherianRing R] [Module.Finite R M]
    (f : R) (hf : ∀ p ∈ associatedPrimes R M, (∃ q ∈ associatedPrimes R M, q < p) → f ∈ p) :
    Function.Bijective (IsLocalizedModule.map (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ Module.embeddedPart R M))
        (Module.embeddedPart R M).mkQ) := by
  refine ⟨?_, IsLocalizedModule.map_surjective _ _ _ _ (Submodule.mkQ_surjective _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk',
      IsLocalizedModule.mk'_eq_zero'] at hx
    obtain ⟨⟨s', a, rfl⟩, hs'⟩ := hx
    simp only [Submonoid.smul_def, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hs'
    obtain ⟨n, hn⟩ := Module.exists_pow_smul_eq_zero_of_mem_embeddedPart hf hs'
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero']
    refine ⟨⟨f ^ (n + a), n + a, rfl⟩, ?_⟩
    show f ^ (n + a) • m = 0
    rw [pow_add, mul_smul]
    exact hn

end Main

section Localized

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (f : R)

/-- `u • (m / s) = 0` in `M_f` for some `u ∉ Q` iff `r • m = 0` for some `r ∉ Q ∩ R`. -/
theorem Module.exists_smul_mk_eq_zero_iff (Q : PrimeSpectrum (Localization.Away f)) (m : M)
    (s : Submonoid.powers f) :
    (∃ u ∉ Q.asIdeal, u • LocalizedModule.mk m s = 0) ↔
      ∃ r ∉ (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) Q).asIdeal, r • m = 0 := by
  constructor
  · rintro ⟨u, hu, hum⟩
    obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (Submonoid.powers f) u
    have h1 : LocalizedModule.mk (r • m) s = 0 := by
      have : (algebraMap R (Localization.Away f) r) • LocalizedModule.mk m s = 0 := by
        rw [← hrt, mul_comm, mul_smul, hum, smul_zero]
      rwa [algebraMap_smul, LocalizedModule.smul'_mk] at this
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero'] at h1
    obtain ⟨⟨c, hc⟩, hcrm⟩ := h1
    refine ⟨c * r, ?_, by rw [mul_smul]; exact hcrm⟩
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_mul, ← hrt]
    intro hmem
    rcases Q.isPrime.mem_or_mem hmem with h | h
    · exact Ideal.notMem_of_isUnit _ (IsLocalization.map_units (Localization.Away f) ⟨c, hc⟩) h
    rcases Q.isPrime.mem_or_mem h with h | h
    · exact hu h
    · exact Ideal.notMem_of_isUnit _ (IsLocalization.map_units (Localization.Away f) t) h
  · rintro ⟨r, hr, hrm⟩
    refine ⟨algebraMap R (Localization.Away f) r, hr, ?_⟩
    rw [algebraMap_smul, LocalizedModule.smul'_mk, hrm, LocalizedModule.zero_mk]

theorem Module.mem_support_localizedModule_away_iff (Q : PrimeSpectrum (Localization.Away f)) :
    Q ∈ Module.support (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) ↔
      PrimeSpectrum.comap (algebraMap R (Localization.Away f)) Q ∈ Module.support R M := by
  constructor
  · intro h
    rw [Module.mem_support_iff'] at h ⊢
    obtain ⟨n, hn⟩ := h
    induction n using LocalizedModule.induction_on with
    | h m s =>
      refine ⟨m, fun r hr hrm ↦ ?_⟩
      obtain ⟨u, hu, hum⟩ := (Module.exists_smul_mk_eq_zero_iff f Q m s).mpr ⟨r, hr, hrm⟩
      exact hn u hu hum
  · intro h
    rw [Module.mem_support_iff'] at h ⊢
    obtain ⟨m, hm⟩ := h
    refine ⟨LocalizedModule.mk m 1, fun u hu hum ↦ ?_⟩
    obtain ⟨r, hr, hrm⟩ := (Module.exists_smul_mk_eq_zero_iff f Q m 1).mp ⟨u, hu, hum⟩
    exact hm r hr hrm

theorem Module.minimal_support_localizedModule_away_iff (Q : PrimeSpectrum (Localization.Away f)) :
    Minimal (· ∈ Module.support (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) Q ↔
      Minimal (· ∈ Module.support R M)
        (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) Q) := by
  have hemb :=
    PrimeSpectrum.localization_comap_isEmbedding (Localization.Away f) (Submonoid.powers f)
  have hle : ∀ Q₁ Q₂ : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap R (Localization.Away f)) Q₁ ≤
        PrimeSpectrum.comap (algebraMap R (Localization.Away f)) Q₂ ↔ Q₁ ≤ Q₂ := by
    intro Q₁ Q₂
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hemb.isInducing.specializes_iff]
  have hrange :=
    PrimeSpectrum.localization_comap_range (Localization.Away f) (Submonoid.powers f)
  constructor
  · rintro ⟨hQ, hmin⟩
    refine ⟨(Module.mem_support_localizedModule_away_iff f Q).mp hQ, ?_⟩
    intro y hy hyQ
    have hy' : y ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
      rw [hrange]
      have hQ' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) Q ∈
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) :=
        Set.mem_range_self Q
      rw [hrange] at hQ'
      exact hQ'.mono_right (SetLike.coe_subset_coe.mpr hyQ)
    obtain ⟨Q', rfl⟩ := hy'
    have := hmin ((Module.mem_support_localizedModule_away_iff f Q').mpr hy) ((hle Q' Q).mp hyQ)
    exact (hle Q Q').mpr this
  · rintro ⟨hQ, hmin⟩
    refine ⟨(Module.mem_support_localizedModule_away_iff f Q).mpr hQ, ?_⟩
    intro Q' hQ' hQ'Q
    exact (hle Q Q').mp
      (hmin ((Module.mem_support_localizedModule_away_iff f Q').mp hQ') ((hle Q' Q).mpr hQ'Q))

/-- If `q` is a minimal prime over `I` and `f ∈ q`, then `r * f ^ n ∈ I` for some `r ∉ q`. -/
theorem Module.embeddedPart.exists_mul_pow_mem_of_mem_minimalPrimes {I q : Ideal R} (hq : q ∈ I.minimalPrimes)
    {g : R} (hg : g ∈ q) : ∃ r ∉ q, ∃ n : ℕ, r * g ^ n ∈ I := by
  have hqp : q.IsPrime := hq.isPrime
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime q) q I hq
  have hmem : algebraMap R (Localization.AtPrime q) g ∈
      (I.map (algebraMap R (Localization.AtPrime q))).radical := by
    rw [hrad]
    exact Ideal.mem_map_of_mem _ hg
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hmem
  rw [← map_pow, IsLocalization.mem_map_algebraMap_iff q.primeCompl] at hn
  obtain ⟨⟨⟨a, ha⟩, s⟩, hs⟩ := hn
  rw [← map_mul] at hs
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists q.primeCompl _).mp hs
  refine ⟨c * s, fun h ↦ (hqp.mem_or_mem h).elim c.2 s.2, n, ?_⟩
  have : (c : R) * s * g ^ n = c * a := by rw [mul_assoc, mul_comm (s : R), hc]
  rw [this]
  exact I.mul_mem_left _ ha

theorem Module.mk_mem_localized_embeddedPart_iff (m : M) (s : Submonoid.powers f) :
    LocalizedModule.mk m s ∈ (Module.embeddedPart R M).localized (Submonoid.powers f) ↔
      ∃ n : ℕ, f ^ n • m ∈ Module.embeddedPart R M := by
  rw [Submodule.mem_localized']
  constructor
  · rintro ⟨m', hm', t, hmt⟩
    rw [← IsLocalizedModule.mk_eq_mk', LocalizedModule.mk_eq] at hmt
    obtain ⟨u, hu⟩ := hmt
    obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
    obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
    refine ⟨a + b, ?_⟩
    have : f ^ (a + b) • m = u • t • m := by
      rw [pow_add, mul_smul, Submonoid.smul_def, Submonoid.smul_def, ha, hb]
    rw [this, ← hu]
    exact (Module.embeddedPart R M).smul_mem _ ((Module.embeddedPart R M).smul_mem _ hm')
  · rintro ⟨n, hn⟩
    refine ⟨f ^ n • m, hn, ⟨f ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩ * s, ?_⟩
    rw [← IsLocalizedModule.mk_eq_mk']
    exact LocalizedModule.mk_cancel_common_left ⟨f ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩ s m

theorem Module.exists_pow_smul_mem_embeddedPart_iff [IsNoetherianRing R] [Module.Finite R M]
    (m : M) :
    (∃ n : ℕ, f ^ n • m ∈ Module.embeddedPart R M) ↔
      ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q → f ∉ q.asIdeal →
        ∃ r ∉ q.asIdeal, r • m = 0 := by
  constructor
  · rintro ⟨n, hn⟩ q hq hfq
    obtain ⟨r, hr, hrm⟩ := (Module.mem_embeddedPart_iff _).mp hn q hq
    refine ⟨r * f ^ n, fun h ↦ ?_, by rw [mul_smul]; exact hrm⟩
    rcases q.isPrime.mem_or_mem h with h | h
    · exact hr h
    · exact hfq (q.isPrime.mem_of_pow_mem n h)
  · intro h
    have hfin := Module.finite_setOf_minimal_support (R := R) (M := M)
    have key : ∀ q : ↥{q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
        ∃ n : ℕ, ∃ r ∉ q.1.asIdeal, (r * f ^ n) • m = 0 := by
      rintro ⟨q, hq⟩
      by_cases hfq : f ∈ q.asIdeal
      · obtain ⟨r, hr, n, hrn⟩ := Module.embeddedPart.exists_mul_pow_mem_of_mem_minimalPrimes
          ((Module.minimal_support_iff q).mp hq) hfq
        exact ⟨n, r, hr, Module.mem_annihilator.mp hrn m⟩
      · obtain ⟨r, hr, hrm⟩ := h q hq hfq
        exact ⟨0, r, hr, by rw [pow_zero, mul_one]; exact hrm⟩
    choose nfun hn using key
    have : Finite ↥{q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q} := hfin.to_subtype
    obtain ⟨N, hN⟩ := (Set.finite_range nfun).bddAbove
    refine ⟨N, ?_⟩
    rw [Module.mem_embeddedPart_iff]
    intro q hq
    obtain ⟨r, hr, hrm⟩ := hn ⟨q, hq⟩
    refine ⟨r, hr, ?_⟩
    have hle : nfun ⟨q, hq⟩ ≤ N := hN (Set.mem_range_self _)
    have hpow : f ^ N = f ^ (N - nfun ⟨q, hq⟩) * f ^ nfun ⟨q, hq⟩ := (pow_sub_mul_pow f hle).symm
    calc r • f ^ N • m = f ^ (N - nfun ⟨q, hq⟩) • ((r * f ^ nfun ⟨q, hq⟩) • m) := by
          rw [smul_smul, smul_smul, hpow]
          congr 1
          ring
      _ = 0 := by rw [hrm, smul_zero]

theorem Module.embeddedPart_localized' [IsNoetherianRing R] [Module.Finite R M] :
    (Module.embeddedPart R M).localized (Submonoid.powers f) =
      Module.embeddedPart (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [Module.mk_mem_localized_embeddedPart_iff, Module.exists_pow_smul_mem_embeddedPart_iff,
      Module.mem_embeddedPart_iff]
    have hrange :=
      PrimeSpectrum.localization_comap_range (Localization.Away f) (Submonoid.powers f)
    constructor
    · intro h Q hQ
      rw [Module.exists_smul_mk_eq_zero_iff]
      refine h _ ((Module.minimal_support_localizedModule_away_iff f Q).mp hQ) ?_
      have hQ' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) Q ∈
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) :=
        Set.mem_range_self Q
      rw [hrange] at hQ'
      exact fun hf ↦ Set.disjoint_left.mp hQ' (Submonoid.mem_powers f) hf
    · intro h q hq hfq
      have hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
        rw [hrange]
        refine Set.disjoint_left.mpr ?_
        rintro x ⟨n, rfl⟩ hx
        exact hfq (q.isPrime.mem_of_pow_mem n hx)
      obtain ⟨Q, rfl⟩ := hq'
      have := h Q ((Module.minimal_support_localizedModule_away_iff f Q).mpr hq)
      rwa [Module.exists_smul_mk_eq_zero_iff] at this

end Localized

/- Stacks 02M6: `K = embeddedPart` is the largest among the submodules whose support is nowhere dense in
   `Supp M`; `M' = M/K` has the same support as `M` and no embedded associated primes; when `f` lies in all
   embedded associated primes of `M`, `M_f → M'_f` is an isomorphism. -/

theorem Module.embeddedPart_spec (R M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsGreatest {K : Submodule R M |
        IsNowhereDense (Subtype.val ⁻¹' Module.support R K : Set ↥(Module.support R M))}
      (Module.embeddedPart R M) ∧
    Module.support R (M ⧸ Module.embeddedPart R M) = Module.support R M ∧
    Module.HasNoEmbeddedPrimes R (M ⧸ Module.embeddedPart R M) ∧
    ∀ f : R, (∀ p ∈ associatedPrimes R M, (∃ q ∈ associatedPrimes R M, q < p) → f ∈ p) →
      Function.Bijective (IsLocalizedModule.map (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ Module.embeddedPart R M))
        (Module.embeddedPart R M).mkQ) :=
  ⟨⟨Module.embeddedPart_isNowhereDense_support, fun K' hK' ↦
      Module.le_embeddedPart_of_isNowhereDense K' hK'⟩,
    Module.support_quotient_embeddedPart, Module.hasNoEmbeddedPrimes_quotient_embeddedPart,
    fun f hf ↦ Module.bijective_localizedMap_mkQ_embeddedPart f hf⟩

/- Stacks 02M7: the construction commutes with localization, `(M')_f = (M_f)'`; at the level of submodules:
   the localization of `K(M)` at `f` equals `K(M_f)`. -/

theorem Module.embeddedPart_localized (R M : Type u) [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (f : R) :
    (Module.embeddedPart R M).localized (Submonoid.powers f) =
      Module.embeddedPart (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) :=
  Module.embeddedPart_localized' f

end
