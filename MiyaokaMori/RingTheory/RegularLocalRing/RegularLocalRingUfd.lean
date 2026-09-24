import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.InvertibleOfLocalFreeRankOne
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00np
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nq
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks0afs
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks0afz
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Nakayama
import Mathlib.Algebra.Module.FinitePresentation

/-! # Regular local rings are UFDs (Auslander–Buchsbaum)

A regular local ring is a unique factorization domain (Auslander–Buchsbaum); hence the local rings of a smooth
variety are UFDs and codimension-one primes are principal.

References: Stacks 0AG0; needed for Cartier = Weil on smooth varieties (the paper uses `K_X` only as a divisor
class).

The main theorem is assembled from `IsRegularLocalRing.pic_localizationAway_subsingleton` (Stacks 0AFZ, `Pic(R_f)`
trivial) and `Module.Invertible.of_localization_free_rank_one` (finitely presented + locally free of rank `1` at
every prime ⇒ invertible); all other inputs are Mathlib (the criterion Stacks 0AFT
`UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`, Nagata's criterion
`UniqueFactorizationMonoid.iff_localizationAway_of_prime`, invariance of height under localization
`IsLocalization.height_map_of_disjoint` / `IsLocalization.height_under`,
`IsLocalization.AtPrime.ringKrullDim_eq_height`, `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`,
the instance "`Pic` trivial ⇒ invertible modules are free", `Module.Invertible.free_iff_linearEquiv`) or modules of
this library (the domain instance 00NP, quotients regular 00NQ, localizations regular 0AFS).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An ideal isomorphic to the ring as a module is principal: with `g := e.symm 1`, for `a ∈ I` we have
`a = e.symm (e a) = e.symm ((e a) • 1) = (e a) • g`, so `I = (g)`. -/
theorem Ideal.isPrincipal_of_nonempty_linearEquiv {A : Type*} [CommRing A] (I : Ideal A)
    (h : Nonempty (I ≃ₗ[A] A)) : I.IsPrincipal := by
  obtain ⟨e⟩ := h
  refine ⟨((e.symm 1 : I) : A), le_antisymm ?_ ?_⟩
  · intro a ha
    rw [Ideal.mem_span_singleton']
    refine ⟨e ⟨a, ha⟩, ?_⟩
    have hx : (⟨a, ha⟩ : I) = e ⟨a, ha⟩ • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
    have := congrArg Subtype.val hx
    simp only [Submodule.coe_smul, smul_eq_mul] at this
    exact this.symm
  · exact (Ideal.span_singleton_le_iff_mem _).mpr (e.symm 1).2

/-- For an ideal `P` and a prime `Q` of a domain `A`: if `P·A_Q` is a nonzero principal ideal, then the localized
module `LocalizedModule Q.primeCompl P` of `P` at `Q` is a free `A_Q`-module of rank `1`.
Proof: `Algebra.idealMap` identifies the localized module of `P` with `P·A_Q` (`IsLocalizedModule.iso`, first
`A`-linearly, then upgraded to `A_Q`-linear by `LinearEquiv.extendScalarsOfIsLocalization`); a nonzero principal
ideal `P·A_Q ≅ A_Q` (`Ideal.isoBaseOfIsPrincipal`). -/
theorem Ideal.nonempty_localizedModule_linearEquiv_of_map_isPrincipal {A : Type*} [CommRing A]
    [IsDomain A] (P Q : Ideal A) [Q.IsPrime]
    (hP : (P.map (algebraMap A (Localization.AtPrime Q))).IsPrincipal)
    (hne : P.map (algebraMap A (Localization.AtPrime Q)) ≠ ⊥) :
    Nonempty (LocalizedModule Q.primeCompl P ≃ₗ[Localization.AtPrime Q] Localization.AtPrime Q) := by
  have := hP
  let e₁ : LocalizedModule Q.primeCompl P ≃ₗ[A] P.map (algebraMap A (Localization.AtPrime Q)) :=
    IsLocalizedModule.iso Q.primeCompl (Algebra.idealMap P (S := Localization.AtPrime Q))
  let e₂ := e₁.extendScalarsOfIsLocalization Q.primeCompl (Localization.AtPrime Q)
  exact ⟨e₂.trans (Ideal.isoBaseOfIsPrincipal hne).symm⟩

/-- The body of the strong induction on `n = spanFinrank 𝔪 (= dim R)` (the universe is fixed to `u`, because the
induction uses the rings `Localization.Away x`, `Localization.AtPrime Q` in the same universe).

Proof (Stacks 0AG0 / Matsumura Thm 20.3):
1. `R` is a domain (the 00NP instance). If `𝔪 = 0`, `R` is a field with no height-one primes, so `R` is a UFD by
   the criterion 0AFT.
2. Otherwise `𝔪 ≠ 𝔪²` (Nakayama); take `x ∈ 𝔪 ∖ 𝔪²`; `R/xR` is regular (00NQ) hence a domain (00NP), so `(x)` is
   prime and `x` is a prime element.
3. Nagata's criterion (Mathlib `iff_localizationAway_of_prime`): it suffices that `A := R_x` is a UFD; `A` is a
   Noetherian domain, so by 0AFT it suffices that every height-one prime `P` of `A` is principal.
4. For every prime `Q` of `A`: `A_Q ≅ R_q` (`q = Q ∩ R`), `R_q` is regular (0AFS) so `A_Q` is regular; `x ∉ q`
   (`x` is invertible in `A`) while `x ∈ 𝔪`, so `q ⊊ 𝔪` and `dim A_Q = ht q < ht 𝔪 = dim R = n`; the induction
   hypothesis gives that `A_Q` is a UFD. `P·A_Q` is either the unit ideal (`P ⊄ Q`) or a height-one prime (`P ≤ Q`;
   heights are preserved by localization); in both cases it is a nonzero principal ideal, so the localization of
   `P` at `Q` is free of rank `1`.
5. `P` is finitely presented over the Noetherian ring `A`, so by `Module.Invertible.of_localization_free_rank_one`
   it is an invertible `A`-module.
6. `Pic(A) = Pic(R_x)` is trivial (Stacks 0AFZ), so `P` is free, `P ≅ A`, and `P` is principal. -/
theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = n → UniqueFactorizationMonoid R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ hn
  classical
  have : IsDomain R := inferInstance
  -- Step 1: the field case `𝔪 = ⊥`.
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
    intro p hp hph
    exfalso
    apply Ideal.ne_bot_of_height_eq_one hph
    exact le_bot_iff.mp (hm ▸ IsLocalRing.le_maximalIdeal hp.ne_top)
  -- Step 2: pick `x ∈ 𝔪 ∖ 𝔪²`; it is a prime element.
  obtain ⟨x, hxm, hx2⟩ : ∃ x ∈ IsLocalRing.maximalIdeal R, x ∉ IsLocalRing.maximalIdeal R ^ 2 := by
    by_contra hcon
    push Not at hcon
    apply hm
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    rw [Ideal.smul_eq_mul, ← pow_two]
    exact hcon
  have hx0 : x ≠ 0 := fun h => hx2 (h ▸ zero_mem _)
  have hxprime : Prime x := by
    rw [← Ideal.span_singleton_prime hx0, ← Ideal.Quotient.isDomain_iff_prime]
    have := IsRegularLocalRing.quotient_span_singleton hxm hx2
    infer_instance
  -- Step 3: Nagata's criterion reduces to `A := R_x`; then Stacks 0AFT on `A`.
  rw [UniqueFactorizationMonoid.iff_localizationAway_of_prime hxprime]
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hx0
  have : IsNoetherianRing (Localization.Away x) :=
    IsLocalization.isNoetherianRing (Submonoid.powers x) (Localization.Away x) inferInstance
  have : IsRegularRing R := IsRegularLocalRing.isRegularRing R
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro P hP hP1
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hP1
  have : Module.FinitePresentation (Localization.Away x) P :=
    Module.finitePresentation_of_finite (Localization.Away x) P
  -- Step 4–5: `P` is an invertible module.
  have hinv : Module.Invertible (Localization.Away x) P := by
    apply Module.Invertible.of_localization_free_rank_one
    intro Q hQ
    -- `A_Q ≅ R_q` is a regular local ring of dimension `ht q < n`.
    have : IsRegularLocalRing (Localization.AtPrime (Ideal.under R Q)) :=
      IsRegularRing.isRegularLocalRing_localization (Ideal.under R Q)
    have : IsRegularLocalRing (Localization.AtPrime Q) :=
      IsRegularLocalRing.of_ringEquiv
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (Submonoid.powers x) Q).toRingEquiv
    have hxq : x ∉ Ideal.under R Q := by
      intro hxq
      exact hQ.ne_top (Q.eq_top_of_isUnit_mem hxq
        (IsLocalization.map_units (Localization.Away x) ⟨x, Submonoid.mem_powers x⟩))
    have hqm : Ideal.under R Q < IsLocalRing.maximalIdeal R :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (fun h => hxq (h ▸ hxm))
    have h4 : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) = ringKrullDim R :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim
    have h5 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    have hmfin : (IsLocalRing.maximalIdeal R).FiniteHeight := by
      rw [Ideal.finiteHeight_iff]
      right
      intro htop
      have h7 : ((⊤ : ℕ∞) : WithBot ℕ∞) =
          ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
        rw [← htop]; exact h4.trans h5.symm
      have h8 : (⊤ : ℕ∞) = ((IsLocalRing.maximalIdeal R).spanFinrank : ℕ∞) := by exact_mod_cast h7
      exact absurd h8 (ENat.top_ne_natCast _)
    have hlt : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank < n := by
      have h1 : ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime Q) := IsRegularLocalRing.spanFinrank_maximalIdeal
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q,
        ← IsLocalization.height_under (Submonoid.powers x) Q] at h1
      have h3 : (Ideal.under R Q).height < (IsLocalRing.maximalIdeal R).height :=
        Ideal.height_strict_mono_of_isPrime_of_isPrime hqm
      have h6 : ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank : WithBot ℕ∞) <
          ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
        h1.trans_lt ((WithBot.coe_lt_coe.mpr h3).trans_eq (h4.trans h5.symm))
      rw [← hn]
      exact_mod_cast h6
    have hufd : UniqueFactorizationMonoid (Localization.AtPrime Q) :=
      ih _ hlt (Localization.AtPrime Q) rfl
    -- `P·A_Q` is a nonzero principal ideal.
    have hPQne : P.map (algebraMap (Localization.Away x) (Localization.AtPrime Q)) ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective
        (IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors)]
      exact hPbot
    have hPQprinc : (P.map (algebraMap (Localization.Away x) (Localization.AtPrime Q))).IsPrincipal := by
      by_cases hPQ' : P ≤ Q
      · have hdisj : Disjoint (Q.primeCompl : Set (Localization.Away x)) (P : Set (Localization.Away x)) := by
          rw [Set.disjoint_left]
          intro a ha haP
          exact ha (hPQ' haP)
        have : (P.map (algebraMap (Localization.Away x) (Localization.AtPrime Q))).IsPrime :=
          IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hP hdisj
        apply UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
        rw [IsLocalization.height_map_of_disjoint Q.primeCompl P hdisj, hP1]
      · have htop : P.map (algebraMap (Localization.Away x) (Localization.AtPrime Q)) = ⊤ := by
          obtain ⟨a, haP, haQ⟩ := SetLike.not_le_iff_exists.mp hPQ'
          exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haP)
            (IsLocalization.map_units (Localization.AtPrime Q) (⟨a, haQ⟩ : Q.primeCompl))
        rw [htop]
        infer_instance
    exact Ideal.nonempty_localizedModule_linearEquiv_of_map_isPrincipal P Q hPQprinc hPQne
  -- Step 6: `Pic(R_x)` is trivial, so `P ≅ A` and `P` is principal.
  have : Subsingleton (CommRing.Pic (Localization.Away x)) :=
    IsRegularLocalRing.pic_localizationAway_subsingleton R x
  have : Module.Free (Localization.Away x) P := inferInstance
  exact Ideal.isPrincipal_of_nonempty_linearEquiv P
    (Module.Invertible.free_iff_linearEquiv.mp inferInstance)

/-- **Regular local rings are UFDs** (Auslander–Buchsbaum; Stacks 0AG0, Matsumura Thm 20.3). `IsDomain R` is
supplied by the instance from Stacks 00NP. For the proof see
`IsRegularLocalRing.uniqueFactorizationMonoid_of_spanFinrank_eq` (strong induction on `dim R`). -/
theorem IsRegularLocalRing.uniqueFactorizationMonoid (R : Type*) [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] : UniqueFactorizationMonoid R :=
  IsRegularLocalRing.uniqueFactorizationMonoid_of_spanFinrank_eq _ R rfl

end
