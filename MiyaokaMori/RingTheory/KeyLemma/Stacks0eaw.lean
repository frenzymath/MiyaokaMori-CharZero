import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameOrd
import MiyaokaMori.RingTheory.KeyLemma.TameOrdEqHsym
import MiyaokaMori.RingTheory.KeyLemma.FinsumHsymEqZero
import MiyaokaMori.RingTheory.KeyLemma.ComapHeight
import MiyaokaMori.RingTheory.KeyLemma.HsymEqZeroOfMaximal

/-! # Stacks 0EAW: the Key Lemma in the nonzerodivisor case

Stacks 0EAW: let `A` be a two-dimensional Noetherian local domain with finite normalization, and
`a, b ∈ A ∖ 0`. Then `Σ_{ht q = 1} ord_{A/q}(∂_{A_q}(a, b)) = 0`.

Reference: Stacks 0EAW (chow-lemma-key-nonzerodivisors). The first paragraph of the original uses
0EAG + 0EAV to build a finite local extension `B`; here the normalization `Ã` is assumed finite, so we
take `B = Ã` directly (semi-local, two-dimensional, normal), and paragraphs two to four of the original are
transferred verbatim to "`B`-modules, `A`-lengths" (each `B_𝔭` is a DVR, `m_i = 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Algebra A B] [Module.Finite A B]

/-- The fibre sum `q ↦ Σ_{𝔭 ∈ MinPrimes(ab), 𝔭 ∩ A = q} Hsym 𝔭` has finite support: where it is nonzero,
`q` is the contraction of some `𝔭 ∈ MinPrimes(ab)`, and `MinPrimes(ab)` is finite
(`KeyLemma.finite_MinPrimes`). (Stacks 0EAW, first paragraph: "the sum is finite".) -/
theorem finite_support_fiber_finsum_Hsym (a b : A) :
    (Function.support fun q : {q : PrimeSpectrum A // q.asIdeal.height = 1} =>
      ∑ᶠ 𝔭 : {𝔭 : MinPrimes (algebraMap A B a * algebraMap A B b) //
          𝔭.1.asIdeal.comap (algebraMap A B) = q.1.asIdeal},
        Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1.1).Finite := by
  classical
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Finite (MinPrimes (algebraMap A B a * algebraMap A B b)) := finite_MinPrimes _
  have : Fintype (MinPrimes (algebraMap A B a * algebraMap A B b)) := Fintype.ofFinite _
  let c : MinPrimes (algebraMap A B a * algebraMap A B b) → PrimeSpectrum A :=
    fun 𝔭 => PrimeSpectrum.comap (algebraMap A B) 𝔭.1
  refine Set.Finite.subset (Finset.finite_toSet
    (((Finset.univ : Finset (MinPrimes (algebraMap A B a * algebraMap A B b))).image c).subtype
      fun p : PrimeSpectrum A => p.asIdeal.height = 1)) ?_
  intro q hq
  rw [Function.mem_support] at hq
  rw [Finset.mem_coe, Finset.mem_subtype, Finset.mem_image]
  by_contra hne
  apply hq
  have : IsEmpty {𝔭 : MinPrimes (algebraMap A B a * algebraMap A B b) //
      𝔭.1.asIdeal.comap (algebraMap A B) = q.1.asIdeal} := by
    refine ⟨fun 𝔭 => hne ⟨𝔭.1, Finset.mem_univ _, ?_⟩⟩
    exact PrimeSpectrum.ext 𝔭.2
  exact finsum_of_isEmpty _

/-- **Regrouping of the second paragraph of Stacks 0EAW**: `A` a two-dimensional Noetherian local domain,
`B` a normal domain, finite over `A` with `A → B` injective, `a, b ∈ A ∖ 0`. Then
`Σ_{ht q = 1} Σ_{𝔭 ∈ MinPrimes(ab), 𝔭 ∩ A = q} e_A(B/(abB_𝔭 ∩ B), a, b) = 0`.

Proof: `MinPrimes(ab)` is finite (`finite_MinPrimes`); the support of the outer `finsum` lies in the
image set `{𝔭 ∩ A}`, so it becomes a `Finset` sum; regrouping along the fibres of `𝔭 ↦ 𝔭 ∩ A`
(`Finset.sum_fiberwise_eq_sum_filter`) gives `Σ_{𝔭 : ht(𝔭 ∩ A) = 1} Hsym 𝔭`; the remaining `𝔭` satisfy
`𝔭 ∩ A = 𝔪_A` (`comap_height_eq_one_or_eq_maximalIdeal`; `𝔭 ≠ 0` since `ab ∈ 𝔭`, `ab ≠ 0`), where
`Hsym 𝔭 = 0` (`Hsym_eq_zero_of_comap_eq_maximalIdeal`), so the sum equals `Σ_{all 𝔭} Hsym 𝔭 = 0`
(`finsum_Hsym_eq_zero`). -/
theorem finsum_fiber_finsum_Hsym_eq_zero [IsDomain A] [IsLocalRing A] [FaithfulSMul A B]
    (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1},
      ∑ᶠ 𝔭 : {𝔭 : MinPrimes (algebraMap A B a * algebraMap A B b) //
          𝔭.1.asIdeal.comap (algebraMap A B) = q.1.asIdeal},
        Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1.1 = 0 := by
  classical
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Finite (MinPrimes (algebraMap A B a * algebraMap A B b)) := finite_MinPrimes _
  have : Fintype (MinPrimes (algebraMap A B a * algebraMap A B b)) := Fintype.ofFinite _
  have ha' : algebraMap A B a ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr ha
  have hb' : algebraMap A B b ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hb
  set t := algebraMap A B a * algebraMap A B b with ht
  have ht0 : t ≠ 0 := mul_ne_zero ha' hb'
  let c : MinPrimes t → PrimeSpectrum A := fun 𝔭 => PrimeSpectrum.comap (algebraMap A B) 𝔭.1
  let P : PrimeSpectrum A → Prop := fun p => p.asIdeal.height = 1
  let s : Finset (PrimeSpectrum A) := (Finset.univ : Finset (MinPrimes t)).image c
  let F : PrimeSpectrum A → ℤ := fun p =>
    ∑ᶠ 𝔭 : {𝔭 : MinPrimes t // 𝔭.1.asIdeal.comap (algebraMap A B) = p.asIdeal},
      Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1.1
  -- total sum over MinPrimes(ab) vanishes (0EA9)
  have h0 : ∑ 𝔭 : MinPrimes t, Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1 = 0 := by
    rw [← finsum_eq_sum_of_fintype]
    exact (finsum_Hsym_eq_zero (A := A) hA.le ha' hb').2
  -- fibre sums as Finset sums
  have hfib : ∀ p : PrimeSpectrum A,
      F p = ∑ 𝔭 ∈ Finset.univ with c 𝔭 = p, Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1 := by
    intro p
    show ∑ᶠ 𝔭 : {𝔭 : MinPrimes t // 𝔭.1.asIdeal.comap (algebraMap A B) = p.asIdeal},
      Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1.1 = _
    rw [finsum_eq_sum_of_fintype]
    refine (Finset.sum_subtype (p := fun 𝔭 : MinPrimes t => 𝔭.1.asIdeal.comap (algebraMap A B) = p.asIdeal)
      _ (fun 𝔭 => ?_) (fun 𝔭 => Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1)).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, c, PrimeSpectrum.ext_iff,
      PrimeSpectrum.comap_asIdeal]
  -- support of the outer sum
  have hsupp : (Function.support fun q : {q : PrimeSpectrum A // q.asIdeal.height = 1} => F q.1)
      ⊆ ↑(s.subtype P) := by
    intro q hq
    rw [Function.mem_support] at hq
    rw [Finset.mem_coe, Finset.mem_subtype, Finset.mem_image]
    by_contra hne
    apply hq
    have : IsEmpty {𝔭 : MinPrimes t // 𝔭.1.asIdeal.comap (algebraMap A B) = q.1.asIdeal} := by
      refine ⟨fun 𝔭 => hne ⟨𝔭.1, Finset.mem_univ _, ?_⟩⟩
      exact PrimeSpectrum.ext 𝔭.2
    exact finsum_of_isEmpty _
  -- primes with Hsym ≠ 0 contract to height-one primes
  have hht : ∀ 𝔭 : MinPrimes t, Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1 ≠ 0 → P (c 𝔭) := by
    intro 𝔭 hne
    have hmem : t ∈ 𝔭.1.asIdeal := 𝔭.2.1.2 (Ideal.mem_span_singleton_self t)
    have hbot : 𝔭.1.asIdeal ≠ ⊥ := by
      intro hb0
      rw [hb0] at hmem
      exact ht0 ((Ideal.mem_bot).mp hmem)
    rcases comap_height_eq_one_or_eq_maximalIdeal (B := B) hA 𝔭.1.asIdeal hbot with h1 | hm
    · exact h1
    · exact absurd (Hsym_eq_zero_of_comap_eq_maximalIdeal (A := A) 𝔭.1 𝔭.2 hm) hne
  calc ∑ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1}, F q.1
      = ∑ q ∈ s.subtype P, F q.1 := finsum_eq_sum_of_support_subset _ hsupp
    _ = ∑ p ∈ s with P p, F p := Finset.sum_subtype_eq_sum_filter F
    _ = ∑ p ∈ s with P p, ∑ 𝔭 ∈ Finset.univ with c 𝔭 = p,
          Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1 :=
        Finset.sum_congr rfl fun p _ => hfib p
    _ = ∑ 𝔭 ∈ Finset.univ with c 𝔭 ∈ (s.filter P),
          Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1 :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ = ∑ 𝔭 ∈ Finset.univ with P (c 𝔭), Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1 := by
        refine Finset.sum_congr (Finset.filter_congr fun 𝔭 _ => ?_) fun _ _ => rfl
        simp only [s, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
          exists_apply_eq_apply]
    _ = ∑ 𝔭 : MinPrimes t, Hsym A (algebraMap A B a) (algebraMap A B b) 𝔭.1 :=
        Finset.sum_filter_of_ne fun 𝔭 _ hne => hht 𝔭 hne
    _ = 0 := h0

end KeyLemma

end

/-- Proof. Let `B := integralClosure A K` and `ã, b̃` the images of `a, b` in `B`.
1. `KeyLemma.tameOrd_eq_exp_neg_finsum_Hsym`: for every `q` of height `1`,
   `tameOrd q a b = exp (−Σ_{𝔭 ∈ MinPrimes(ãb̃), 𝔭 ∩ A = q} Hsym A ã b̃ 𝔭)`.
2. `KeyLemma.exp_finsum` + `finsum_neg_distrib`: `∏ᶠ q, exp (−S_q) = exp (−Σᶠ_q S_q)`; finiteness of the
   support is `KeyLemma.finite_support_fiber_finsum_Hsym`.
3. `KeyLemma.finsum_fiber_finsum_Hsym_eq_zero`: `Σᶠ_q S_q = 0` (regrouping along the fibres `𝔭 ↦ 𝔭 ∩ A`;
   `finsum_Hsym_eq_zero`, `comap_height_eq_one_or_eq_maximalIdeal`, `Hsym_eq_zero_of_comap_eq_maximalIdeal`).
Instances on `B`: `IsIntegrallyClosed` by `integralClosure.isIntegrallyClosedOfFiniteExtension` (`L = K`),
`FaithfulSMul` since `A → K` is injective.
Edge cases: if `a` or `b` is a unit, `MinPrimes` may be empty (`ab` a unit) or contain only the prime
factors of `b`; the formula holds as stated. If `a = b`, `Hsym(a,a)` vanishes termwise. -/
theorem Ring.tameOrd_finprod_eq_one_of_mem (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∏ᶠ q : {q : PrimeSpectrum A // q.asIdeal.height = 1},
      Ring.tameOrd A hA hfin q
        (Units.mk0 (algebraMap A (FractionRing A) a)
          ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha))
        (Units.mk0 (algebraMap A (FractionRing A) b)
          ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hb)) = 1 := by
  have : IsIntegrallyClosed (integralClosure A (FractionRing A)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) (FractionRing A) (L := FractionRing A)
  have : FaithfulSMul A (integralClosure A (FractionRing A)) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A (FractionRing A))).mpr (by
      intro x y hxy
      apply IsFractionRing.injective A (FractionRing A)
      have := congrArg (algebraMap (integralClosure A (FractionRing A)) (FractionRing A)) hxy
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this)
  have hsupp : (Function.support fun q : {q : PrimeSpectrum A // q.asIdeal.height = 1} =>
      -(∑ᶠ 𝔭 : {𝔭 : KeyLemma.MinPrimes
            (algebraMap A (integralClosure A (FractionRing A)) a *
              algebraMap A (integralClosure A (FractionRing A)) b) //
            𝔭.1.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A))) = q.1.asIdeal},
          KeyLemma.Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
            (algebraMap A (integralClosure A (FractionRing A)) b) 𝔭.1.1)).Finite := by
    refine (KeyLemma.finite_support_fiber_finsum_Hsym (B := integralClosure A (FractionRing A))
      a b).subset ?_
    intro q hq
    simp only [Function.mem_support, ne_eq, neg_eq_zero] at hq ⊢
    exact hq
  rw [finprod_congr (fun q => KeyLemma.tameOrd_eq_exp_neg_finsum_Hsym A hA hB hfin q a b ha hb),
    ← KeyLemma.exp_finsum _ hsupp, finsum_neg_distrib,
    KeyLemma.finsum_fiber_finsum_Hsym_eq_zero (B := integralClosure A (FractionRing A)) hA a b ha hb,
    neg_zero, WithZero.exp_zero]
