import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs

/-! # Additivity of the order in symbolic powers

For `B_𝔭` a DVR: `a ∈ 𝔭^(e) ∖ 𝔭^(e+1)`, `b ∈ 𝔭^(f) ∖ 𝔭^(f+1) ⇒ ab ∈ 𝔭^(e+f) ∖ 𝔭^(e+f+1)` (`ord_𝔭` is
additive).

Reference: Stacks 00PD (the valuation of a DVR is additive); used in the second paragraph of 0EAW for
`(M_i)_{𝔮_i} = A_{𝔮_i}/(π^{e+f})`.
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {B : Type u} [CommRing B] [IsDomain B]
  (𝔭 : Ideal B) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

/-- Proof: `x ∈ symbPow 𝔭 n ↔ n ≤ addVal (B_𝔭) (algebraMap x)` (`Ideal.mem_comap` +
`IsDiscreteValuationRing.addVal_le_iff_dvd` / `maximalIdeal ^ n = span {ϖ ^ n}`), then
`AddValuation.map_mul`. -/
theorem mul_mem_symbPow {a b : B} {e f : ℕ} (ha : a ∈ symbPow 𝔭 e) (ha' : a ∉ symbPow 𝔭 (e + 1))
    (hb : b ∈ symbPow 𝔭 f) (hb' : b ∉ symbPow 𝔭 (f + 1)) :
    a * b ∈ symbPow 𝔭 (e + f) ∧ a * b ∉ symbPow 𝔭 (e + f + 1) := by
  -- Work in the DVR `R = B_𝔭` with a uniformizer `ϖ`: `x ∈ 𝔭^(n) ↔ ϖ ^ n ∣ f x`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔭)
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  have hprime : Prime ϖ := hϖ.prime
  unfold symbPow at ha ha' hb hb' ⊢
  simp only [Ideal.mem_comap, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    map_mul] at ha ha' hb hb' ⊢
  -- Split off the exact powers: `f a = ϖ ^ e * a'`, `f b = ϖ ^ f * b'` with `ϖ ∤ a'`, `ϖ ∤ b'`.
  obtain ⟨a', hfa⟩ := ha
  obtain ⟨b', hfb⟩ := hb
  rw [hfa] at ha' ⊢
  rw [hfb] at hb' ⊢
  have ha'' : ¬ ϖ ∣ a' := fun h => ha' (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have hb'' : ¬ ϖ ∣ b' := fun h => hb' (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  refine ⟨?_, ?_⟩
  · rw [pow_add]
    exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _)
  · intro h
    have hrw : ϖ ^ e * a' * (ϖ ^ f * b') = ϖ ^ (e + f) * (a' * b') := by ring
    rw [hrw, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)] at h
    rcases hprime.dvd_or_dvd h with h | h
    · exact ha'' h
    · exact hb'' h

end KeyLemma

end
