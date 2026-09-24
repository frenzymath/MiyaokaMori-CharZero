import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00np
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nq
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Nakayama

/-! # Regular local rings of dimension at most two are UFDs

A regular local ring of dimension `≤ 2` is a UFD (without Auslander–Buchsbaum, global dimension, or finite free
resolutions).

References: steps 2–3 of the proof of Stacks 0AG0 (take `x ∈ 𝔪 ∖ 𝔪²`, `R/xR` regular), concluded directly in
`dim ≤ 2`; the criterion "a Noetherian domain is a UFD ⟺ all height-one primes are principal" = Stacks 0AFT
(Mathlib `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`); Lemma U2 is the standard Nakayama
descent argument (as in the descent step of the proof of Matsumura, *Commutative Ring Theory*, Thm 20.1).

The general-dimension result (module `RegularLocalRingUfd`, via 0AFZ / Auslander–Buchsbaum) is still needed for
`K_X` in dimension `n`; only users that need a UFD in `dim ≤ 2` use this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A finitely generated submodule with at most one generator is principal.

Proof: take a finite set `s` of `spanFinrank` many generators
(`Submodule.FG.exists_span_finset_card_eq_spanFinrank`); if `s.card = 0` then `N = ⊥`
(`Submodule.spanFinrank_eq_zero_iff_eq_bot`), which is principal; if `s.card = 1`,
`Submodule.spanFinrank_eq_one_iff` gives principality directly. -/
theorem Submodule.isPrincipal_of_spanFinrank_le_one {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {N : Submodule R M} (hfg : N.FG) (h : N.spanFinrank ≤ 1) : N.IsPrincipal := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · rw [(Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp h0]
    infer_instance
  · exact ((Submodule.spanFinrank_eq_one_iff N).mp h1).1

/-- **Lemma U2** (Nakayama descent). `R` a Noetherian local ring, `x ∈ 𝔪`, `R/xR` a principal ideal ring, `p` a
prime with `x ∉ p`; then `p` is principal.

Reference: the descent step in the proof of Stacks 0AG0; standard form in the proof of Matsumura, *Commutative
Ring Theory*, Thm 20.1.

Proof:
1. The image `p·(R/xR)` of `p` in `R/xR` is principal; take a generator and lift it: `ḡ = g mod x`, `g ∈ p`
   (`Ideal.mem_map_iff_of_surjective` + `Ideal.Quotient.mk_surjective`).
2. For `a ∈ p`: `ā ∈ (ḡ)`, write `ā = r̄·ḡ`, so `a − r·g ∈ (x)`, i.e. `a − r·g = s·x`.
3. `a ∈ p` and `r·g ∈ p` (since `g ∈ p`) ⇒ `s·x ∈ p`; `p` prime and `x ∉ p` ⇒ `s ∈ p`.
4. Hence `a = r·g + s·x ∈ (g) + 𝔪·p`, i.e. `p ≤ (g) ⊔ 𝔪·p`.
5. `p` is finitely generated (Noetherian) and `𝔪 ≤ jacobson ⊥` (local ring); Nakayama
   (`Submodule.le_of_le_smul_of_le_jacobson_bot`) ⇒ `p ≤ (g)`; with `g ∈ p`, `p = (g)`.

Edge cases: for `p = ⊥` the conclusion is trivial and the proof goes through (`g` can be `0`); if `R` is a field
then `𝔪 = ⊥`, `x = 0`, and `x ∉ p` forces `p ≠ ⊥`, contradicting `p ≤ 𝔪 = ⊥` — the hypotheses cannot be
satisfied. `R` need not be a domain. -/
theorem Ideal.isPrincipal_of_isPrincipalIdealRing_quotient_span_singleton
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hq : IsPrincipalIdealRing (R ⧸ Ideal.span {x}))
    {p : Ideal R} (hp : p.IsPrime) (hxp : x ∉ p) : p.IsPrincipal := by
  classical
  obtain ⟨ĝ, hĝ⟩ := hq.principal (p.map (Ideal.Quotient.mk (Ideal.span {x})))
  have hmem : ĝ ∈ p.map (Ideal.Quotient.mk (Ideal.span {x})) := by
    rw [hĝ]; exact Submodule.mem_span_singleton_self _
  obtain ⟨g, hgp, hgeq⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hmem
  have key : p ≤ Ideal.span {g} ⊔ (IsLocalRing.maximalIdeal R) • p := by
    intro a ha
    have ha' : ∃ c : R ⧸ Ideal.span {x},
        c * ĝ = Ideal.Quotient.mk (Ideal.span {x}) a := by
      have h1 : Ideal.Quotient.mk (Ideal.span {x}) a ∈
          p.map (Ideal.Quotient.mk (Ideal.span {x})) := Ideal.mem_map_of_mem _ ha
      rw [hĝ] at h1
      simpa only [Submodule.mem_span_singleton, smul_eq_mul] using h1
    obtain ⟨c, hc⟩ := ha'
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hsub : a - r * g ∈ Ideal.span {x} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hgeq, hc, sub_self]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hsub
    have hsp : s ∈ p := by
      have hmul : s * x ∈ p := by
        rw [hs]; exact p.sub_mem ha (p.mul_mem_left r hgp)
      exact (hp.mem_or_mem hmul).resolve_right hxp
    refine Submodule.mem_sup.mpr ⟨r * g, Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩, s * x, ?_, ?_⟩
    · rw [mul_comm]
      exact Submodule.smul_mem_smul hx hsp
    · rw [hs]; ring
  have hle : p ≤ Ideal.span {g} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian p)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) key
  exact ⟨g, le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr hgp)⟩

/-- **A regular local ring of dimension `≤ 2` is a UFD** (the `dim R ≤ 2` version of Auslander–Buchsbaum;
`IsDomain R` is supplied by the instance `IsRegularLocalRing.isDomain`).

Reference: steps 2–3 of the proof of Stacks 0AG0 + Stacks 0AFT (Mathlib
`UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`).

Proof (show that every height-one prime `p` is principal):
* If `𝔪 ⊆ 𝔪² ∪ p`, then `𝔪 ≤ 𝔪²` or `𝔪 ≤ p` by `Ideal.subset_union`.
  - `𝔪 ≤ 𝔪² = 𝔪 • 𝔪`: Nakayama ⇒ `𝔪 = ⊥`, so `p ≤ 𝔪 = ⊥` and `p = ⊥` is principal.
  - `𝔪 ≤ p`: `p ≤ 𝔪`, so `p = 𝔪`; `height 𝔪 = dim R` (`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`) and
    `height p = 1` give `dim R = 1`, regularity gives `spanFinrank 𝔪 = 1`, so `𝔪 = p` is principal.
* Otherwise take `x ∈ 𝔪`, `x ∉ 𝔪²`, `x ∉ p`. By `IsRegularLocalRing.quotient_span_singleton` (Stacks 00NQ),
  `R/xR` is regular local, and by the instance `IsRegularLocalRing.isDomain` (Stacks 00NP) it is a domain.
  `spanFinrank 𝔪 = dim R ≤ 2` and `spanFinrank (𝔪/x) + 1 ≤ spanFinrank 𝔪`
  (`IsLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le`), so `spanFinrank (𝔪/x) ≤ 1`, i.e.
  `𝔪/x` is principal; by the DVR characterization TFAE for Noetherian local domains (Mathlib
  `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`, item 4 ⇒ item 0), `R/xR` is a principal ideal ring.
  Lemma U2 gives that `p` is principal.

Edge cases: `dim R = 0` (a field): no height-one primes, the criterion holds vacuously; `dim R = 1` (DVR): the
second branch above. The zero ring is not a local ring (`IsLocalRing` includes `Nontrivial`). -/
theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 2) :
    UniqueFactorizationMonoid R := by
  classical
  have : IsDomain R := inferInstance
  have hd2 : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 2 := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)]; exact h
  have hdim : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 2 := by exact_mod_cast hd2
  rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
  intro p hp hph
  have : p.IsPrime := hp
  by_cases hsub : ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) ⊆
      ((IsLocalRing.maximalIdeal R ^ 2 : Ideal R) : Set R) ∪ ((p : Ideal R) : Set R)
  · rcases Ideal.subset_union.mp hsub with hle | hle
    · have hbot : IsLocalRing.maximalIdeal R = ⊥ := by
        refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
          (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) ?_
          (IsLocalRing.maximalIdeal_le_jacobson _)
        rw [Ideal.smul_eq_mul, ← pow_two]
        exact hle
      have hpb : p = ⊥ :=
        le_bot_iff.mp (by rw [← hbot]; exact IsLocalRing.le_maximalIdeal hp.ne_top)
      rw [hpb]; infer_instance
    · have hpm : p = IsLocalRing.maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hle
      have h1 : ringKrullDim R = 1 := by
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hpm, hph]; rfl
      have hsf : (IsLocalRing.maximalIdeal R).spanFinrank = 1 := by
        have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
        rw [h1] at h2
        exact_mod_cast h2
      rw [hpm]
      exact ((Submodule.spanFinrank_eq_one_iff _).mp hsf).1
  · obtain ⟨x, hxm, hxni⟩ := Set.not_subset.mp hsub
    simp only [Set.mem_union, SetLike.mem_coe, not_or] at hxni
    obtain ⟨hx2, hxp⟩ := hxni
    have hxm' : x ∈ IsLocalRing.maximalIdeal R := hxm
    have hreg : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
      IsRegularLocalRing.quotient_span_singleton hxm' hx2
    have : IsDomain (R ⧸ Ideal.span {x}) := inferInstance
    have hq1 : (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ 1 := by
      have h3 := IsLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le hxm' hx2
      omega
    have hqp : (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).IsPrincipal :=
      Submodule.isPrincipal_of_spanFinrank_le_one (IsNoetherian.noetherian _) hq1
    have hpir : IsPrincipalIdealRing (R ⧸ Ideal.span {x}) :=
      ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R ⧸ Ideal.span {x})).out 4 0).mp hqp
    exact Ideal.isPrincipal_of_isPrincipalIdealRing_quotient_span_singleton hxm' hpir hp hxp

end
