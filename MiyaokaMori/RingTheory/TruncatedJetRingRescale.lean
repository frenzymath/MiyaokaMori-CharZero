import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra

/-! # Rescaling the parameter of a truncated jet ring

The parameter rescaling `rescale c : t ↦ c · t` (`c ∈ S`) of the truncated ring `S[t]/(t^(r+1))` is
a ring homomorphism; it multiplies the coefficient of order `n` by `c^n` (`coeff_rescale`), preserves
the constant term, satisfies `rescale 1 = id` and `rescale (c*d) = rescale c ∘ rescale d`, and commutes
with the coefficient map `map`.

This fixes the weight convention of the paper ("`t ↦ λt` gives the coefficient of order `q` weight
`q`", §2 of the paper; Demailly [Dem11, (0.3)]) as a ring homomorphism together with a `@[simp]` coefficient formula, from which the
coaction and the grading of the jet algebra are derived. The geometric rescaling `jetBaseRescaling`
is a morphism of `Spec`s and cannot be computed coefficientwise.
-/

set_option autoImplicit false

universe u

noncomputable section

namespace MiyaokaMori.Jet.TruncatedJetRing

open Polynomial

variable {S : Type u} [CommRing S] (r : ℕ)

-- `rescale_wellDefined` / `rescale` / `rescale_projection` / `coeff_rescale` / `ext_coeff` /
-- `rescale_one` / `rescale_mul` live in the module defining the truncated ring. The three lemmas
-- below mention `MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.{epsilon, eta}`, whose module is downstream
-- of that one, so they are stated here.

/-- Rescaling does not change the constant term. -/
@[simp] theorem epsilon_rescale (c : S) (x : TruncatedJetRing S r) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (rescale r c x) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  show (p.comp (C c * X)).eval 0 = p.eval 0
  simp [Polynomial.eval_comp]

/-- Rescaling fixes the constant coefficients. -/
@[simp] theorem rescale_eta (c a : S) :
    rescale r c (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a := by
  show MiyaokaMori.Jet.jetProjection S r ((C a).comp (C c * X)) = _
  rw [Polynomial.C_comp]; rfl

/-- For `c = 0` the rescaling degenerates to "take the constant term and embed it back" (the limit
of the `𝔸¹`-action at `0` is the retraction onto the base section). -/
theorem rescale_zero (x : TruncatedJetRing S r) :
    rescale r (0 : S) x =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  show MiyaokaMori.Jet.jetProjection S r (p.comp (C 0 * X)) =
    MiyaokaMori.Jet.jetProjection S r (C (p.eval 0))
  rw [map_zero, zero_mul, Polynomial.comp_zero]

end MiyaokaMori.Jet.TruncatedJetRing

end
