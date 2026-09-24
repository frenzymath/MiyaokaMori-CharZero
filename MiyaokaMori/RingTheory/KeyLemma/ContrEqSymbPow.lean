import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs

/-! # The contraction of a principal ideal at a prime is a symbolic power

If `B_𝔭` is a DVR and `t ∈ 𝔭^(n) ∖ 𝔭^(n+1)`, then `tB_𝔭 ∩ B = 𝔭^(n)` (in a DVR, `(t) = 𝔪^{ord t}`).

References: third paragraph of the proof of Stacks 0EAW
("`M_i ⊂ (M_i)_{𝔮_i} = A_{𝔮_i}/(π_i^{e_i+f_i})`"); Stacks 00PD.
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {B : Type u} [CommRing B] [IsDomain B]

/-- Proof: in the DVR `R`, `Ideal.span {x} = maximalIdeal R ^ n` when `addVal x = n`
(`IsDiscreteValuationRing.ideal_eq_span_pow_irreducible` + the characterization of `addVal`); take
`Ideal.comap` on both sides. Edge case `n = 0`: `t ∉ 𝔭`, `t` is a unit in `R`, both sides are `⊤`. -/
theorem contr_eq_symbPow (𝔭 : PrimeSpectrum B) [IsDiscreteValuationRing (Localization.AtPrime 𝔭.asIdeal)]
    {t : B} {n : ℕ} (ht : t ∈ symbPow 𝔭.asIdeal n) (ht' : t ∉ symbPow 𝔭.asIdeal (n + 1)) :
    contr 𝔭 t = symbPow 𝔭.asIdeal n := by
  -- Work in the DVR `R = B_𝔭`; write `f t` for the image of `t`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔭.asIdeal)
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭.asIdeal) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  unfold symbPow at ht ht' ⊢
  unfold contr
  rw [Ideal.mem_comap, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ht ht'
  rw [hmax, Ideal.span_singleton_pow]
  -- `f t ≠ 0` since `0 ∈ 𝔪^(n+1)`.
  have hne : algebraMap B (Localization.AtPrime 𝔭.asIdeal) t ≠ 0 := by
    intro h0
    exact ht' (h0 ▸ dvd_zero _)
  have hbot : Ideal.span {algebraMap B (Localization.AtPrime 𝔭.asIdeal) t} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  -- `(f t) = (ϖ^m)` for some `m`; the two hypotheses force `m = n`.
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
  have hassoc := Ideal.span_singleton_eq_span_singleton.mp hm
  rw [hassoc.dvd_iff_dvd_right, pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at ht ht'
  have hmn : m = n := by omega
  rw [hm, hmn]

end KeyLemma

end
