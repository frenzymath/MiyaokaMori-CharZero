import MiyaokaMori.Prelude
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Adic valuations of a Dedekind domain along a ring isomorphism

`Θ : R ≃+* S` an isomorphism of Dedekind domains, `v : HeightOneSpectrum R`,
`v' := equivOfRingEquiv Θ v` (so `v'.asIdeal = v.asIdeal.map Θ`). Then `v'.intValuation (Θ r) = v.intValuation r`
and, for compatible fraction fields `ψ : K ≃+* K'`, `v'.valuation K' (ψ x) = v.valuation K x`.

Proof: `intValuation r = exp (-multiplicity v.asIdeal (span {r}))` (Mathlib
`intValuation_eq_exp_neg_multiplicity`), and `Ideal.map Θ` preserves powers, `span {r}`, and divisibility
(`dvd ↔ ≥` in a Dedekind domain), hence multiplicities (`emultiplicity_eq_emultiplicity_iff`). Extend to `K`
by writing `x = a / b`. Helper for the vanishing of the tame-cycle sum in the key formula.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]

theorem equivOfRingEquiv_asIdeal (Θ : R ≃+* S) (v : HeightOneSpectrum R) :
    (equivOfRingEquiv Θ v).asIdeal = v.asIdeal.map (Θ : R →+* S) := by
  show Ideal.comap (Θ.symm : S →+* R) v.asIdeal = _
  exact Ideal.comap_symm Θ

/-- `Ideal.map` along a ring isomorphism preserves divisibility of ideals in Dedekind domains. -/
theorem map_dvd_map_iff (Θ : R ≃+* S) (I J : Ideal R) :
    I.map (Θ : R →+* S) ∣ J.map (Θ : R →+* S) ↔ I ∣ J := by
  have hb : Function.Bijective (Θ : R →+* S) := Θ.bijective
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap,
    Ideal.comap_map_of_bijective _ hb]

theorem intValuation_equivOfRingEquiv (Θ : R ≃+* S) (v : HeightOneSpectrum R) (r : R) :
    (equivOfRingEquiv Θ v).intValuation (Θ r) = v.intValuation r := by
  by_cases hr : r = 0
  · subst hr; rw [map_zero, map_zero, map_zero]
  have hr' : Θ r ≠ 0 := (map_ne_zero_iff Θ Θ.injective).mpr hr
  rw [intValuation_eq_exp_neg_multiplicity _ hr, intValuation_eq_exp_neg_multiplicity _ hr']
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  have hspan : Ideal.span {Θ r} = (Ideal.span {r}).map (Θ : R →+* S) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  rw [equivOfRingEquiv_asIdeal, hspan, ← Ideal.map_pow, map_dvd_map_iff]

variable {K K' : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra S K']
  [IsFractionRing S K']

theorem valuation_equivOfRingEquiv (Θ : R ≃+* S) (ψ : K ≃+* K')
    (hψ : ∀ r : R, ψ (algebraMap R K r) = algebraMap S K' (Θ r)) (v : HeightOneSpectrum R) (x : K) :
    (equivOfRingEquiv Θ v).valuation K' (ψ x) = v.valuation K x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  rw [map_div₀, hψ, hψ, map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_equivOfRingEquiv,
    intValuation_equivOfRingEquiv]

end IsDedekindDomain.HeightOneSpectrum

end
