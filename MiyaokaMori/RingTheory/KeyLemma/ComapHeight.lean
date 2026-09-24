import MiyaokaMori.Prelude

/-! # Contraction of a nonzero prime of an integral extension of a two-dimensional local domain

Let `A` be a two-dimensional Noetherian local domain, `B ⊇ A` a domain integral over `A`, and `𝔭 ≠ 0` a
prime of `B`. Then `𝔭 ∩ A` has height `1`, or `𝔭 ∩ A = 𝔪_A`.

References: Stacks 00GT (the contraction of a nonzero prime under an integral extension is nonzero);
00KG (in a local ring a prime of height `= dim` is the maximal ideal).
-/

set_option autoImplicit false

universe u

noncomputable section

namespace KeyLemma

end KeyLemma

/-- Proof: `p := 𝔭 ∩ A` is prime and `p ≠ ⊥` (`Ideal.comap_ne_bot_of_integral_mem`; `A ⊆ B` integral,
`B` a domain). `A` is a domain ⇒ `ht p ≥ 1` (`⊥ < p`). `ht p ≤ dim A = 2`
(`Ideal.height_le_ringKrullDim_of_ne_top`). If `ht p = 2` then `p = 𝔪_A`: otherwise `p < 𝔪_A` gives
`ht 𝔪_A ≥ 3 > dim A` (`Ideal.height_strict_mono_of_isPrime`; in Lean directly via
`Ideal.height_eq_ringKrullDim_iff`, with `FiniteRingKrullDim A` obtained from `hA` by
`finiteRingKrullDim_iff_ne_bot_and_top`). -/
theorem KeyLemma.comap_height_eq_one_or_eq_maximalIdeal {A B : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : ringKrullDim A = 2) [CommRing B] [IsDomain B] [Algebra A B]
    [FaithfulSMul A B] [Algebra.IsIntegral A B] (𝔭 : Ideal B) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    (𝔭.comap (algebraMap A B)).height = 1 ∨ 𝔭.comap (algebraMap A B) = IsLocalRing.maximalIdeal A := by
  set p := 𝔭.comap (algebraMap A B) with hp
  have hpP : p.IsPrime := Ideal.IsPrime.comap _
  have hfin : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr
      ⟨by rw [hA]; exact WithBot.coe_ne_bot, by rw [hA]; decide⟩
  have hne : p ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have hle : (p.height : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := by
    have := Ideal.height_le_ringKrullDim_of_ne_top (R := A) hpP.ne_top
    rwa [hA] at this
  have hle' : p.height ≤ 2 := WithBot.coe_le_coe.mp hle
  have hpos : p.height ≠ 0 := by rwa [Ne, Ideal.height_eq_zero_iff_eq_bot]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by decide) hle')
  rw [← hn] at hle' hpos ⊢
  have hn2 : n = 1 ∨ n = 2 := by
    have := (Nat.cast_le (α := ℕ∞)).mp (by exact_mod_cast hle' : (n : ℕ∞) ≤ (2 : ℕ))
    have := (Nat.cast_ne_zero (R := ℕ∞)).mp hpos
    omega
  rcases hn2 with rfl | rfl
  · left; rfl
  · right
    exact Ideal.height_eq_ringKrullDim_iff.mp (by rw [hA, ← hn]; rfl)

namespace KeyLemma

end KeyLemma

end
