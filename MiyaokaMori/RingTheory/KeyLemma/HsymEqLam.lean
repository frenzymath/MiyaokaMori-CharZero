import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.SymbPowMul
import MiyaokaMori.RingTheory.KeyLemma.ContrEqSymbPow
import MiyaokaMori.RingTheory.KeyLemma.HerbrandSymbPow

/-! # The multiplicity `Hsym` as a difference of lengths

The previous statement in the notation of `Hsym`: for `𝔭 ∈ Spec B` with `B_𝔭` a DVR,
`Hsym A a b 𝔭 = λ_𝔭(y₂) − λ_𝔭(y₁)`.

Reference: first sentence of the third paragraph of Stacks 0EAW (`(M_i)_{𝔮_i} = A_{𝔮_i}/(π^{e+f})`, i.e.
`abB_𝔭 ∩ B = 𝔭^(e+f)`).
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B]

theorem Hsym_eq_lam_sub (𝔭 : PrimeSpectrum B) [IsDiscreteValuationRing (Localization.AtPrime 𝔭.asIdeal)]
    (hfl : ∀ y ∉ 𝔭.asIdeal, Module.length A (B ⧸ (𝔭.asIdeal ⊔ Ideal.span {y})) ≠ ⊤) {a b : B} {e f : ℕ}
    (ha : a ∈ symbPow 𝔭.asIdeal e) (ha' : a ∉ symbPow 𝔭.asIdeal (e + 1))
    (hb : b ∈ symbPow 𝔭.asIdeal f) (hb' : b ∉ symbPow 𝔭.asIdeal (f + 1))
    {y₁ y₂ : B} (hy₁ : y₁ ∉ 𝔭.asIdeal) (hy₂ : y₂ ∉ 𝔭.asIdeal)
    (hy : y₁ * b ^ e = (-1) ^ (e * f) * y₂ * a ^ f) :
    Hsym A a b 𝔭 = (lam A 𝔭.asIdeal y₂ : ℤ) - (lam A 𝔭.asIdeal y₁ : ℤ) := by
  obtain ⟨h1, h2⟩ := mul_mem_symbPow 𝔭.asIdeal ha ha' hb hb'
  unfold Hsym
  rw [contr_eq_symbPow 𝔭 h1 h2]
  exact (herbrand_symbPow_eq 𝔭.asIdeal hfl ha ha' hb hb' hy₁ hy₂ hy).2

end KeyLemma

end
