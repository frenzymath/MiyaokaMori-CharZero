import MiyaokaMori.Prelude
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Artinian.Ring

/-! # A power of the maximal ideal lies in an ideal of finite colength

In a Noetherian local ring `A`, if `A ⧸ J` has finite length then `𝔪^n ⊆ J` for some `n`.
This supplies the hypothesis `𝔪ⁿ ⊆ I` of Stacks 0AGT in the blowup-improvement step of Stacks 0AHH
(`I := I_x`, finite length by `lengthSum_ne_top`).

Source: Stacks 00J5/00J8 (a Noetherian module of finite length is Artinian; in an Artinian local
ring the maximal ideal is nilpotent).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

noncomputable section

/-- `A` Noetherian local, `length_A (A ⧸ J) < ∞` ⇒ `𝔪^n ≤ J` for some `n`: `A ⧸ J` is an Artinian
ring (`isFiniteLength_iff_isNoetherian_isArtinian`, `isArtinian_of_tower`), so its Jacobson radical
`= 𝔪 (A ⧸ J)` is nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`); pull back along the
quotient map. -/
theorem IsLocalRing.exists_maximalIdeal_pow_le_of_length_ne_top {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (J : Ideal A) (h : Module.length A (A ⧸ J) ≠ ⊤) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ n ≤ J := by
  by_cases hJ : J = ⊤
  · exact ⟨0, by simp [hJ]⟩
  have hfl : IsFiniteLength A (A ⧸ J) := Module.length_ne_top_iff.mp h
  obtain ⟨-, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  have : IsArtinianRing (A ⧸ J) := isArtinian_of_tower A hart
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A ⧸ J)
  refine ⟨n, ?_⟩
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top,
    ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hn
  exact hn

end
