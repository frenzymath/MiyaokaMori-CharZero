import MiyaokaMori.Prelude

/-! # The adic valuation as the order in the localization

For a height-one prime `v` of a Dedekind domain `B` (fraction field `K`) and `b ∈ B ∖ 0`: Mathlib's
`v`-adic valuation satisfies `v(b) = exp(−ord_{B_v}(b))`, where `ord_{B_v}(b) = length_{B_v}(B_v/b)`
(Mathlib `Ring.ord`, `B_v = Localization.AtPrime v.asIdeal`).

References: the `ord_{B_{𝔪_j}}` in the statement of Stacks 02MJ; 00PD (the valuation of a DVR is the
length); the proof of 0EAN uses it to replace `HeightOneSpectrum.valuation` by the `ord` of 02MJ.
-/

set_option autoImplicit false

universe u

noncomputable section

/-- Proof: `B_v` is a DVR (Mathlib `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, needs
`v.ne_bot`).
Left-hand side: `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap` turns
`v.valuation K (algebraMap B K b)` into `v.intValuation b`, and `intValuation_eq_exp_neg_multiplicity` gives
`exp(−multiplicity v.asIdeal (span {b}))`.
Right-hand side: `x := algebraMap B B_v b ≠ 0`; `Ring.ord_ne_top` gives that `ord_{B_v} x` is finite, with
`toNat` `m`; `Ring.ord_eq_addVal` gives `addVal_{B_v} x = m`.
Bridge (for every `k`): `v^k ∣ (b) ⟺ b ∈ v^k` (`Ideal.dvd_span_singleton`) `⟺ x ∈ 𝔪^k` (Mathlib
`IsLocalization.AtPrime.under_maximalIdeal_pow`: `(𝔪_{B_v}^k) ∩ B = v^k`, the correspondence between
`v`-primary ideals and ideals of `B_v`) `⟺ ϖ^k ∣ x` (`Irreducible.maximalIdeal_eq`,
`Ideal.span_singleton_pow`) `⟺ k ≤ addVal_{B_v} x = m` (`addVal_le_iff_dvd`, `Irreducible.addVal_pow`).
Taking `k = m, m+1`, `multiplicity_eq_of_dvd_of_not_dvd` gives `multiplicity = m`.
Edge cases: `b` a unit ⇒ both sides are `exp 0 = 1`. `b = 0` is excluded (otherwise the right-hand side has
`Ring.ord = ⊤`, `toNat = 0`, while the left-hand side is `0`). -/
theorem Ring.TameSymbol.valuation_eq_exp_neg_ord_localization {B K : Type u} [CommRing B]
    [IsDedekindDomain B] [Field K] [Algebra B K] [IsFractionRing B K]
    (v : IsDedekindDomain.HeightOneSpectrum B) (b : B) (hb : b ≠ 0) :
    IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap B K b) =
      WithZero.exp (-((Ring.ord (Localization.AtPrime v.asIdeal)
        (algebraMap B (Localization.AtPrime v.asIdeal) b)).toNat : ℤ)) := by
  set S := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B v.ne_bot S
  set x : S := algebraMap B S b with hx
  have hx0 : x ≠ 0 := by
    rw [hx, map_ne_zero_iff _ (IsLocalization.injective S v.asIdeal.primeCompl_le_nonZeroDivisors)]
    exact hb
  -- left-hand side: Mathlib gives `v(b) = exp(−multiplicity v (b))`
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hb]
  congr 3
  -- right-hand side: `ord_S x = addVal_S x` is finite, call it `m`
  set m := (Ring.ord S x).toNat with hm
  have hord : Ring.ord S x = (m : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx0))).symm
  have haddVal : IsDiscreteValuationRing.addVal S x = (m : ℕ∞) := by
    rw [← Ring.ord_eq_addVal, hord]
  -- the key bridge: `b ∈ v^k ⟺ x ∈ 𝔪_S^k ⟺ ϖ^k ∣ x ⟺ k ≤ addVal_S x`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have key : ∀ k : ℕ, v.asIdeal ^ k ∣ Ideal.span {b} ↔ (k : ℕ∞) ≤ m := by
    intro k
    rw [Ideal.dvd_span_singleton, ← IsLocalization.AtPrime.under_maximalIdeal_pow v.asIdeal S k,
      Ideal.mem_under, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow, ← hx, haddVal]
  apply multiplicity_eq_of_dvd_of_not_dvd
  · exact (key m).mpr le_rfl
  · rw [key]
    exact_mod_cast Nat.not_succ_le_self m

end
