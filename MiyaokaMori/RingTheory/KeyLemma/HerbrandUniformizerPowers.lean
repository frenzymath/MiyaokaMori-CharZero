import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.Length.FiniteLengthCriterion
import MiyaokaMori.RingTheory.Length.PeriodicComplexPowers

/-! # Herbrand quotient of `(B/𝔭^(e+f), π^e, π^f)` vanishes

Stacks 0EAB in the present situation: `π ∈ 𝔭^(1) ∖ 𝔭^(2)`, `M = B/𝔭^(e+f)`; then
`e_A(M, π^e, π^f) = 0` and the cohomology has finite length.

References: Stacks 0EAB (chow-lemma-powers-period-length-zero); the `0` in the third equality of the
third paragraph of 0EAW.
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

/-! ## Uniform annihilators on finitely generated submodules -/

theorem mem_submoduleOf_iff {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} {x : q} : x ∈ p.submoduleOf q ↔ (x : M) ∈ p := Iff.rfl

/-- If `K` is finitely generated and every element of `K` is multiplied into `J` by some element of `S`,
then a single element of `S` multiplies all of `K` into `J`. -/
theorem exists_smul_mem_of_fg {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (S : Submonoid R) {K J : Submodule R M} (hK : K.FG)
    (h : ∀ k ∈ K, ∃ s ∈ S, s • k ∈ J) : ∃ s ∈ S, ∀ k ∈ K, s • k ∈ J := by
  refine Submodule.fg_induction
    (motive := fun K' _ => K' ≤ K → ∃ s ∈ S, ∀ k ∈ K', s • k ∈ J) ?_ ?_ K hK le_rfl
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := h x (hx (Submodule.mem_span_singleton_self x))
    refine ⟨s, hs, fun k hk => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hk
    rw [smul_comm]
    exact J.smul_mem c hsx
  · intro K₁ K₂ _ _ h₁ h₂ hle
    obtain ⟨s₁, hs₁, h₁⟩ := h₁ (le_sup_left.trans hle)
    obtain ⟨s₂, hs₂, h₂⟩ := h₂ (le_sup_right.trans hle)
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, fun k hk => ?_⟩
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Submodule.mem_sup.mp hk
    have e1 : (s₁ * s₂) • k₁ = s₂ • (s₁ • k₁) := by rw [mul_comm, mul_smul]
    have e2 : (s₁ * s₂) • k₂ = s₁ • (s₂ • k₂) := mul_smul _ _ _
    rw [smul_add, e1, e2]
    exact J.add_mem (J.smul_mem _ (h₁ k₁ hk₁)) (J.smul_mem _ (h₂ k₂ hk₂))

/-! ## Valuation arithmetic of a uniformizer `π` in a DVR -/

section DVR

variable {B : Type u} [CommRing B] [IsDomain B]
  (𝔭 : Ideal B) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

omit [IsDomain B] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)] in
theorem symbPow_zero : symbPow 𝔭 0 = ⊤ := by
  simp only [symbPow, pow_zero, Ideal.one_eq_top, Ideal.comap_top]

/-- `π ∈ 𝔭^(1) ∖ 𝔭^(2) ⇒ 𝔪_{B_𝔭} = (π/1)`: take a uniformizer `ϖ`, `π/1 = ϖ a`, `ϖ² ∤ π/1 ⇒ ϖ ∤ a ⇒ a` is a
unit. -/
theorem maximalIdeal_eq_span_of_uniformizer {π : B} (hπ1 : π ∈ symbPow 𝔭 1)
    (hπ2 : π ∉ symbPow 𝔭 2) :
    IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap B (Localization.AtPrime 𝔭) π} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔭)
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  simp only [symbPow, Ideal.mem_comap, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_one] at hπ1 hπ2
  obtain ⟨a, ha⟩ := hπ1
  rw [ha] at hπ2 ⊢
  rw [hm, Ideal.span_singleton_eq_span_singleton]
  have hu : IsUnit a := by
    rw [← IsLocalRing.notMem_maximalIdeal, hm, Ideal.mem_span_singleton]
    rintro ⟨b, rfl⟩
    exact hπ2 ⟨b, by ring⟩
  exact ⟨hu.unit, by rw [IsUnit.unit_spec]⟩

variable {𝔭}

theorem mem_symbPow_iff_pow_dvd {π : B} (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2)
    (x : B) (n : ℕ) :
    x ∈ symbPow 𝔭 n ↔
      algebraMap B (Localization.AtPrime 𝔭) π ^ n ∣ algebraMap B (Localization.AtPrime 𝔭) x := by
  simp only [symbPow, Ideal.mem_comap, maximalIdeal_eq_span_of_uniformizer 𝔭 hπ1 hπ2,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem algebraMap_uniformizer_ne_zero {π : B} (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2) :
    algebraMap B (Localization.AtPrime 𝔭) π ≠ 0 := by
  intro h
  apply hπ2
  rw [mem_symbPow_iff_pow_dvd hπ1 hπ2, h]
  exact dvd_zero _

/-- `πb ∈ 𝔭^(m+1) ⇒ b ∈ 𝔭^(m)` (`ord π = 1`). -/
theorem mem_symbPow_of_mul_mem {π : B} (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2)
    {b : B} {m : ℕ} (hb : π * b ∈ symbPow 𝔭 (m + 1)) : b ∈ symbPow 𝔭 m := by
  rw [mem_symbPow_iff_pow_dvd hπ1 hπ2] at hb ⊢
  rw [map_mul, pow_succ', mul_dvd_mul_iff_left (algebraMap_uniformizer_ne_zero hπ1 hπ2)] at hb
  exact hb

/-- `x ∈ 𝔭`, `πb ∈ 𝔭^(n) ⇒ xb ∈ 𝔭^(n)` (`x/1 ∈ 𝔪 = (π/1)`). -/
theorem mul_mem_symbPow_of_mem_of_mul_mem {π : B} (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2)
    {x b : B} {n : ℕ} (hx : x ∈ 𝔭) (hb : π * b ∈ symbPow 𝔭 n) : x * b ∈ symbPow 𝔭 n := by
  have hx' : algebraMap B (Localization.AtPrime 𝔭) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 x).mpr hx
  rw [maximalIdeal_eq_span_of_uniformizer 𝔭 hπ1 hπ2, Ideal.mem_span_singleton] at hx'
  obtain ⟨y, hy⟩ := hx'
  rw [mem_symbPow_iff_pow_dvd hπ1 hπ2] at hb ⊢
  rw [map_mul] at hb ⊢
  rw [hy, mul_right_comm]
  exact Dvd.dvd.mul_right hb y

/-- `b ∈ 𝔭^(m) ⇒` there are `s ∉ 𝔭` and `c` with `sb = π^m c` (in `B_𝔭`, `b/1 = (π/1)^m u`; clear
denominators; `B → B_𝔭` is injective). -/
theorem exists_mul_eq_pow_mul_of_mem_symbPow {π : B} (hπ1 : π ∈ symbPow 𝔭 1)
    (hπ2 : π ∉ symbPow 𝔭 2) {b : B} {m : ℕ} (hb : b ∈ symbPow 𝔭 m) :
    ∃ s ∉ 𝔭, ∃ c : B, s * b = π ^ m * c := by
  rw [mem_symbPow_iff_pow_dvd hπ1 hπ2] at hb
  obtain ⟨u, hu⟩ := hb
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj 𝔭.primeCompl u
  simp only at hcs
  refine ⟨s, s.2, c, IsLocalization.injective (Localization.AtPrime 𝔭)
    (Ideal.primeCompl_le_nonZeroDivisors 𝔭) ?_⟩
  rw [map_mul, map_mul, map_pow, hu, mul_comm, mul_assoc, hcs]

end DVR

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B] (𝔭 : Ideal B) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

/-- For `n = m + 1` and `t` = multiplication by `π`, the `A`-length of
`H(t, t^m) = Ker t/(Im t^m ∩ Ker t) ≅ 𝔭^(m)/(π^m B + 𝔭^(m+1))` is finite: write it as the `B`-module
`N = K/(J ∩ K)` (`K = Ker(mult. by π)`, `J = Im(mult. by π^m)`, both `B`-submodules of `B ⧸ 𝔭^(m+1)`);
`N` is annihilated by `𝔭` (`x ∈ 𝔭`, `πb ∈ 𝔭^(m+1) ⇒ xb ∈ 𝔭^(m+1)`) and by some `s ∉ 𝔭` (`K` is finitely
generated and every generator `b` satisfies `b ∈ 𝔭^(m)`, so `sb = π^m c`), hence
`length_ne_top_of_smul_eq_zero` applies. -/
theorem length_H_mulQ_pow_ne_top
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {π : B}
    (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2) (m : ℕ) :
    Module.length A
      (H (mulQ A (symbPow 𝔭 (m + 1)) π) ((mulQ A (symbPow 𝔭 (m + 1)) π) ^ m)) ≠ ⊤ := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  set I := symbPow 𝔭 (m + 1) with hI
  set φ : (B ⧸ I) →ₗ[B] (B ⧸ I) := LinearMap.mulLeft B (Ideal.Quotient.mk I π) with hφ
  set ψ : (B ⧸ I) →ₗ[B] (B ⧸ I) := LinearMap.mulLeft B (Ideal.Quotient.mk I (π ^ m)) with hψ
  set K := LinearMap.ker φ with hK
  set J := LinearMap.range ψ with hJ
  have htm : (mulQ A I π) ^ m = ψ.restrictScalars A := by rw [← mulQ_pow]; rfl
  -- if `k = mk b ∈ K`, then `πb ∈ I`
  have hmemK : ∀ b : B, Ideal.Quotient.mk I b ∈ K → π * b ∈ I := by
    intro b hb
    rw [hK, LinearMap.mem_ker, hφ, LinearMap.mulLeft_apply, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem] at hb
    exact hb
  -- `N := K/(J ∩ K)`, a `B`-module
  let N : Type u := ↥K ⧸ J.submoduleOf K
  let g : ↥(LinearMap.ker (mulQ A I π)) →ₗ[A] N :=
    { toFun := fun x => Submodule.Quotient.mk (⟨x.1, x.2⟩ : K)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨⟨k, hk⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨⟨k, hk⟩, rfl⟩
  have hker : LinearMap.ker g =
      (LinearMap.range ((mulQ A I π) ^ m)).submoduleOf (LinearMap.ker (mulQ A I π)) := by
    ext x
    rw [LinearMap.mem_ker, mem_submoduleOf_iff, htm]
    show Submodule.Quotient.mk (⟨x.1, x.2⟩ : K) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_submoduleOf_iff]
    exact Iff.rfl
  rw [length_H, ← length_eq_relLength g hg hker]
  -- a uniform annihilator `s ∉ 𝔭`
  obtain ⟨s, hs, hsK⟩ : ∃ s ∈ 𝔭.primeCompl, ∀ k ∈ K, s • k ∈ J := by
    refine exists_smul_mem_of_fg 𝔭.primeCompl (IsNoetherian.noetherian K) ?_
    intro k hk
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨s, hs, c, hsc⟩ := exists_mul_eq_pow_mul_of_mem_symbPow hπ1 hπ2
      (mem_symbPow_of_mul_mem hπ1 hπ2 (hmemK b hk))
    refine ⟨s, hs, ?_⟩
    rw [hJ, LinearMap.mem_range]
    refine ⟨Ideal.Quotient.mk I c, ?_⟩
    rw [hψ, LinearMap.mulLeft_apply, ← map_mul, ← hsc, map_mul]
    rfl
  refine length_ne_top_of_smul_eq_zero 𝔭 hfl N s hs 1 ?_ ?_
  · intro x hx n
    rw [pow_one] at hx
    obtain ⟨⟨k, hk⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_submoduleOf_iff]
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective k
    have h0 : x • Ideal.Quotient.mk I b = 0 := by
      show Ideal.Quotient.mk I (x * b) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact mul_mem_symbPow_of_mem_of_mul_mem hπ1 hπ2 hx (hmemK b hk)
    show x • Ideal.Quotient.mk I b ∈ J
    rw [h0]
    exact zero_mem _
  · intro n
    obtain ⟨⟨k, hk⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_submoduleOf_iff]
    exact hsK k hk

/-- Proof: `t := mulQ A (𝔭^(n)) π`, `n = e + f`; `mulQ_pow` replaces `π^e`, `π^f` by `t^e`, `t^f`
(`f = n − e`). For `n = 0`, `M = 0` (`𝔭^(0) = ⊤`) and `herbrand_eq_zero_of_length_ne_top` applies. For
`n > 0` use `PeriodicComplex.herbrand_pow_eq_zero t n _ hfin e _`, whose hypothesis `hfin` is that
`H(t, t^{n−1}) = 𝔭^(n−1)/(π^{n−1}B + 𝔭^(n))` has finite length: it is annihilated by `𝔭`
(`𝔭·𝔭^(n−1) ⊂ 𝔭^(n)`) and by some `s ∉ 𝔭` (in `B_𝔭`, `𝔭^(n−1)B_𝔭 = π^{n−1}B_𝔭`), so
`length_ne_top_of_smul_eq_zero` applies (`length_H_mulQ_pow_ne_top`). -/
theorem herbrand_mulQ_pow_uniformizer
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {π : B}
    (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2) (e f : ℕ) :
    FiniteCohomology (mulQ A (symbPow 𝔭 (e + f)) (π ^ e)) (mulQ A (symbPow 𝔭 (e + f)) (π ^ f)) ∧
      herbrand (mulQ A (symbPow 𝔭 (e + f)) (π ^ e)) (mulQ A (symbPow 𝔭 (e + f)) (π ^ f)) = 0 := by
  rcases Nat.eq_zero_or_pos (e + f) with h0 | hpos
  · -- n = 0: 𝔭^(0) = ⊤, M = 0
    have hM : Module.length A (B ⧸ symbPow 𝔭 (e + f)) ≠ ⊤ := by
      have : Subsingleton (B ⧸ symbPow 𝔭 (e + f)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [h0, symbPow_zero])
      rw [Module.length_eq_zero]
      exact ENat.zero_ne_top
    have htop : π ^ e * π ^ f ∈ symbPow 𝔭 (e + f) := by
      rw [h0, symbPow_zero]; exact Submodule.mem_top
    exact herbrand_eq_zero_of_length_ne_top _ _ (mulQ_comp_eq_zero _ htop)
      (mulQ_comp_eq_zero _ (by rw [mul_comm]; exact htop)) hM
  · obtain ⟨m, hm⟩ : ∃ m, e + f = m + 1 := ⟨e + f - 1, by omega⟩
    have hfin := length_H_mulQ_pow_ne_top 𝔭 hfl hπ1 hπ2 m
    rw [← hm] at hfin
    have key := herbrand_pow_eq_zero (mulQ A (symbPow 𝔭 (e + f)) π) (e + f) hpos
      (by rw [show e + f - 1 = m by omega]; exact hfin) e (Nat.le_add_right e f)
    rw [Nat.add_sub_cancel_left] at key
    rw [mulQ_pow, mulQ_pow]
    exact key

end KeyLemma

end
