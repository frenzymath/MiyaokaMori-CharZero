import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Vanishing of `Hsym` at a prime lying over the maximal ideal

Let `A` be Noetherian local, `B` a finite `A`-algebra which is a domain, and `𝔭 ∈ MinPrimes(ab)` with
`𝔭 ∩ A = 𝔪_A` (`𝔭` is a height-one maximal ideal of `B`; this can happen when `A` is not catenary). Then
`e_A(B/(abB_𝔭 ∩ B), a, b) = 0`.

Reference: Stacks 0EA8 (chow-lemma-finite-periodic-length: the periodic complex of a finite-length
module has `e = 0`).
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B]

/-- Over a Noetherian local ring `A`, a finite module `M` annihilated by `𝔪_A^N` has finite `A`-length (a
special case of Stacks 00KH + 00L5).
Proof: `M` is an `A/𝔪^{N+1}`-module (`Module.IsTorsionBySet.module`), and `A`-submodules coincide with
`A/𝔪^{N+1}`-submodules, so `Module.length_eq_of_surjective` gives `length_A M = length_{A/𝔪^{N+1}} M`.
`𝔪` is the unique minimal prime over `𝔪^{N+1}`, and Noetherian local ⇒ `A/𝔪^{N+1}` Artinian
(`IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`, Stacks 00KH); a finite module over
an Artinian ring is Artinian and Noetherian, hence of finite length (`Module.length_ne_top`). -/
theorem length_ne_top_of_maximalIdeal_pow_smul_eq_zero (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (N : ℕ)
    (hM : ∀ x ∈ IsLocalRing.maximalIdeal A ^ N, ∀ m : M, x • m = 0) :
    Module.length A M ≠ ⊤ := by
  have hM' : ∀ x ∈ IsLocalRing.maximalIdeal A ^ (N + 1), ∀ m : M, x • m = 0 := fun x hx m =>
    hM x (Ideal.pow_le_pow_right (Nat.le_succ N) hx) m
  have htor : Module.IsTorsionBySet A M (IsLocalRing.maximalIdeal A ^ (N + 1) : Ideal A) :=
    fun m x => hM' x.1 x.2 m
  let : Module (A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) M := htor.module
  have : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) M := htor.isScalarTower
  have hmin : IsLocalRing.maximalIdeal A ∈ (IsLocalRing.maximalIdeal A ^ (N + 1)).minimalPrimes := by
    refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal A).isPrime,
      Ideal.pow_le_self (Nat.succ_ne_zero N)⟩, ?_⟩
    intro q hq _
    exact hq.1.le_of_pow_le hq.2
  have : IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1)) M :=
    Module.Finite.of_restrictScalars_finite A _ M
  have hsurj : Function.Surjective (algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (N + 1))) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hsurj]
  exact Module.length_ne_top

/-- Proof. One route: `𝔭 ∩ A = 𝔪_A` and `B` integral over `A` ⇒ `𝔭` maximal
(`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`). The radical of `I := contr 𝔭 (ab)` is `𝔭` (`𝔭` is
minimal over `(ab)`, `I = abB_𝔭 ∩ B` is `𝔭`-primary), and `B` Noetherian ⇒ `𝔭^N ≤ I`
(`Ideal.exists_radical_pow_le_of_fg`). `B/𝔭^N` has finite `A`-length: `𝔭^i/𝔭^{i+1}` is a
finite-dimensional space over `B/𝔭`, and `B/𝔭` is finite-dimensional over `A/𝔪_A`; hence
`length_A(B/I) < ∞` and `PeriodicComplex.herbrand_eq_zero_of_length_ne_top` applies (hypothesis
`mulQ_comp_eq_zero`, `a*b ∈ I`).

The actual route (shorter; no maximality, radicals or `𝔭`-adic filtration):
1. In `B_𝔭` (Noetherian local; `B` is Noetherian by `IsNoetherianRing.of_finite A B`), the minimal primes
   of `(ab)B_𝔭` are exactly `𝔭B_𝔭 = 𝔪_{B_𝔭}` (`IsLocalization.minimalPrimes_map` +
   `Localization.AtPrime.under_maximalIdeal`), so `B_𝔭/(ab)` is Artinian
   (`IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`), hence `𝔪_{B_𝔭}^N ≤ (ab)B_𝔭`
   (`IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`); pulling back, `𝔭^N ≤ I`.
2. `𝔪_A B ≤ 𝔭` (by `hcomap`), so `𝔪_A^N` annihilates `B/I`; `B/I` is a finite `A`-module, and
   `length_ne_top_of_maximalIdeal_pow_smul_eq_zero` gives `length_A(B/I) < ∞`.

Note: the proof does not use `[IsDomain B]` (the statement holds for any finite `A`-algebra `B`); the
instance argument is kept for compatibility with the call sites. -/
theorem Hsym_eq_zero_of_comap_eq_maximalIdeal {a b : B} (𝔭 : PrimeSpectrum B)
    (h𝔭 : 𝔭.asIdeal ∈ (Ideal.span {a * b}).minimalPrimes)
    (hcomap : 𝔭.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    Hsym A a b 𝔭 = 0 := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
  -- Step 1: in B_𝔭 the ideal (ab) has the maximal ideal as its unique minimal prime.
  have hJ : (Ideal.span {a * b}).map (algebraMap B (Localization.AtPrime 𝔭.asIdeal)) =
      Ideal.span {algebraMap B (Localization.AtPrime 𝔭.asIdeal) (a * b)} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmin : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭.asIdeal) ∈
      ((Ideal.span {a * b}).map (algebraMap B (Localization.AtPrime 𝔭.asIdeal))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map 𝔭.asIdeal.primeCompl (Localization.AtPrime 𝔭.asIdeal)]
    show Ideal.under B (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭.asIdeal)) ∈
      (Ideal.span {a * b}).minimalPrimes
    rw [Localization.AtPrime.under_maximalIdeal]
    exact h𝔭
  have : IsArtinianRing (Localization.AtPrime 𝔭.asIdeal ⧸
      (Ideal.span {a * b}).map (algebraMap B (Localization.AtPrime 𝔭.asIdeal))) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  obtain ⟨N, hN⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    ((Ideal.span {a * b}).map (algebraMap B (Localization.AtPrime 𝔭.asIdeal)))
  -- Step 2: 𝔭^N ≤ contr 𝔭 (ab).
  have hpow : 𝔭.asIdeal ^ N ≤ contr 𝔭 (a * b) := by
    intro x hx
    show algebraMap B (Localization.AtPrime 𝔭.asIdeal) x ∈
      Ideal.span {algebraMap B (Localization.AtPrime 𝔭.asIdeal) (a * b)}
    rw [← hJ]
    apply hN
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  -- Step 3: 𝔪_A^N kills B ⧸ contr 𝔭 (ab).
  have hm : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ 𝔭.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hcomap.ge
  have hkill : ∀ x ∈ IsLocalRing.maximalIdeal A ^ N, ∀ m : B ⧸ contr 𝔭 (a * b), x • m = 0 := by
    intro x hx m
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hxB : algebraMap A B x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) ^ N := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B (B ⧸ contr 𝔭 (a * b)),
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact (contr 𝔭 (a * b)).mul_mem_right y (hpow (Ideal.pow_right_mono hm N hxB))
  have : Module.Finite A (B ⧸ contr 𝔭 (a * b)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (contr 𝔭 (a * b))).toLinearMap
      Ideal.Quotient.mk_surjective
  have hlen : Module.length A (B ⧸ contr 𝔭 (a * b)) ≠ ⊤ :=
    length_ne_top_of_maximalIdeal_pow_smul_eq_zero (B ⧸ contr 𝔭 (a * b)) N hkill
  -- Step 4: Stacks 0EA8.
  have hab : a * b ∈ contr 𝔭 (a * b) := Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
  have hba : b * a ∈ contr 𝔭 (a * b) := by rw [mul_comm b a]; exact hab
  unfold Hsym
  exact (herbrand_eq_zero_of_length_ne_top (mulQ A (contr 𝔭 (a * b)) a) (mulQ A (contr 𝔭 (a * b)) b)
    (mulQ_comp_eq_zero _ hab) (mulQ_comp_eq_zero _ hba) hlen).2

end KeyLemma

end
