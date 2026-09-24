import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs

/-! # Factorization of an element of exact order at a prime

If `π ∈ 𝔭^(1) ∖ 𝔭^(2)` and `a ∈ 𝔭^(e) ∖ 𝔭^(e+1)`, then there are `c, u ∈ B ∖ 𝔭` with `c·a = u·π^e`
(fourth paragraph of Stacks 0EAW: multiplying by `c ∉ 𝔮_i` brings the unit `u` of the local
factorization `a = uπ^e` into the ring).

Reference: fourth paragraph of the proof of Stacks 0EAW ("choose c ∈ A, c ∉ 𝔮_i with cu_i, cv_i ∈ A").
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {B : Type u} [CommRing B] [IsDomain B]
  (𝔭 : Ideal B) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

/-- Proof: in the DVR `R = B_𝔭`, take a uniformizer `ϖ` (`exists_irreducible`), `𝔪 = (ϖ)`. The image
`π' ∈ 𝔪 ∖ 𝔪²` of `π` is `π' = ϖ·t` with `t ∉ 𝔪` (otherwise `π' ∈ 𝔪²`), so `t` is a unit, `π'` is
associated to `ϖ`, `π'` is irreducible and `𝔪 = (π')`. `a ≠ 0` (otherwise `a ∈ 𝔭^(e+1)`), and
`eq_unit_mul_pow_irreducible` gives `a = w·π'^n` with `w ∈ Rˣ`; `a ∈ 𝔪^e = (π'^e)` gives `e ≤ n` and
`a ∉ 𝔪^(e+1)` gives `n ≤ e` (`pow_dvd_pow_iff_le`), so `n = e`. `IsLocalization.surj` writes `w` as
`w·c = u` (`c ∉ 𝔭`, `u ∈ B`); `w`, `c` are units in `R` ⇒ `u` is a unit in `R` ⇒ `u ∉ 𝔭`
(`IsLocalization.AtPrime.isUnit_to_map_iff`). Hence in `R`, `c·a = c·w·π'^e = u·π'^e`, which descends to
`B` by `IsLocalization.injective` (`B` a domain, `𝔭.primeCompl ≤ nonZeroDivisors`). The edge case
`e = 0` needs no separate treatment (the same argument gives `n = 0`). -/
theorem exists_mul_eq_mul_pow {π a : B} {e : ℕ} (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2)
    (ha : a ∈ symbPow 𝔭 e) (ha' : a ∉ symbPow 𝔭 (e + 1)) :
    ∃ c u : B, c ∉ 𝔭 ∧ u ∉ 𝔭 ∧ c * a = u * π ^ e := by
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors
  -- the image of π is a uniformizer of R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔭)
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  simp only [symbPow, Ideal.mem_comap, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_one] at hπ1 hπ2
  obtain ⟨t, ht⟩ := hπ1
  have ht_unit : IsUnit t := by
    by_contra hnt
    apply hπ2
    have htm : t ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
      (IsLocalRing.mem_maximalIdeal t).mpr (mem_nonunits_iff.mpr hnt)
    rw [hm, Ideal.mem_span_singleton] at htm
    rw [ht, pow_two]
    exact mul_dvd_mul_left ϖ htm
  have hassoc : Associated ϖ (algebraMap B (Localization.AtPrime 𝔭) π) :=
    ⟨ht_unit.unit, by rw [IsUnit.unit_spec]; exact ht.symm⟩
  have hπirr : Irreducible (algebraMap B (Localization.AtPrime 𝔭) π) := hassoc.irreducible hϖ
  have hm' : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap B (Localization.AtPrime 𝔭) π} := hπirr.maximalIdeal_eq
  simp only [symbPow, Ideal.mem_comap, hm', Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    at ha ha'
  -- a = w * π ^ n in R, and n = e
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply ha'
    rw [map_zero]
    exact dvd_zero _
  have hfa0 : algebraMap B (Localization.AtPrime 𝔭) a ≠ 0 := fun h =>
    ha0 (hinj (by rw [h, map_zero]))
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfa0 hπirr
  have h1 : e ≤ n := by
    rw [hw] at ha
    exact (pow_dvd_pow_iff hπirr.ne_zero hπirr.not_isUnit).mp (Units.dvd_mul_left.mp ha)
  have h2 : n ≤ e := by
    by_contra h
    push Not at h
    apply ha'
    rw [hw]
    exact Units.dvd_mul_left.mpr (pow_dvd_pow _ (Nat.succ_le_of_lt h))
  obtain rfl : n = e := le_antisymm h2 h1
  -- write w = u / c
  obtain ⟨⟨u, c⟩, hcu⟩ := IsLocalization.surj 𝔭.primeCompl (w : Localization.AtPrime 𝔭)
  simp only at hcu
  refine ⟨c, u, c.2, ?_, ?_⟩
  · have hu : IsUnit (algebraMap B (Localization.AtPrime 𝔭) u) := by
      rw [← hcu]
      exact w.isUnit.mul (IsLocalization.map_units (Localization.AtPrime 𝔭) c)
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 u).mp hu
  · apply hinj
    rw [map_mul, map_mul, map_pow, hw, ← hcu]
    ring

end KeyLemma

end
