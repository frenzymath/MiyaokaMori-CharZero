import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# A one-dimensional regular local domain is a DVR

This is the local algebra step in the proof of Proposition 3.2 of the paper, used by
`SmoothProjectiveCurve.closedPoint_coheight_one_and_isDiscreteValuationRing`.
It applies to the actual curve stalk once its regularity and dimension have been proved.
Those geometric assertions remain separate obligations.

Regularity identifies the number of generators of the maximal ideal with the Krull dimension.
In dimension one the maximal ideal is principal and nonzero. The Noetherian local-domain
criterion then gives a principal ideal ring, hence a discrete valuation ring.
The mathematical source is Stacks, Algebra, Lemma `lemma-characterize-dvr` (Tag 00PD).
-/

noncomputable section

universe u

namespace MiyaokaMori.RingTheory

/-- A regular local domain of Krull dimension one is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_regularLocalRing_dimension_one
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hspan : (IsLocalRing.maximalIdeal R).spanFinrank = 1 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨hprincipal, hne⟩ :=
    (Submodule.spanFinrank_eq_one_iff (IsLocalRing.maximalIdeal R)).mp hspan
  let : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 0).mp hprincipal
  exact { not_a_field' := hne }

end MiyaokaMori.RingTheory
