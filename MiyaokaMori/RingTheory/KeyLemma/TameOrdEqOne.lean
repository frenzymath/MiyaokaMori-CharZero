import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameOrd

/-! # The tame symbol of two units is `1`

If `f, g` are units at the height-one prime `q` (`f = a/a′`, `g = b/b′` with `a, a′, b, b′ ∈ A ∖ q`), then
`∂_{A_q}(f, g) = 1`, hence `ord_{A/q}(∂_{A_q}(f,g)) = 0` (`tameOrd = 1` in multiplicative notation).

Reference: end of the statement of Stacks 0EAX ("at any height 1 prime 𝔮 where f, g ∈ A_𝔮^* we have
∂_{A_𝔮}(f, g) = 1").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

/-- Proof: let `R := A_q`. `a, a′ ∉ q ⇒` they are units in `R` (`IsLocalization.map_units` for
`q.asIdeal.primeCompl`), `u := a/a′ ∈ Rˣ`, and `(f : K) = algebraMap R K u`
(`IsScalarTower.algebraMap_apply A R K` + `hf`). Likewise for `g`. Unfold `Ring.tameOrd`, `Ring.tameSymbol`,
`Ring.tameSymbolAt`; for every `v`, `Ring.TameSymbol.valuation_unit_eq_one R v u` gives `v(f) = v(g) = 1`,
`Ring.TameSymbol.localFactor_eq_one` gives local factor `1`; `finprod_one`, `map_one`.
Edge cases: `f = g = 1` is trivial; the conclusion does not depend on the number of maximal ideals of `Ã_q`
over `q`. -/
theorem Ring.tameOrd_eq_one_of_not_mem (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1}) (f g : (FractionRing A)ˣ)
    (hf : ∃ a a' : A, a ∉ q.1.asIdeal ∧ a' ∉ q.1.asIdeal ∧
      (f : FractionRing A) * algebraMap A (FractionRing A) a' = algebraMap A (FractionRing A) a)
    (hg : ∃ b b' : A, b ∉ q.1.asIdeal ∧ b' ∉ q.1.asIdeal ∧
      (g : FractionRing A) * algebraMap A (FractionRing A) b' = algebraMap A (FractionRing A) b) :
    Ring.tameOrd A hA hfin q f g = 1 := by
  obtain ⟨a, a', ha, ha', hf⟩ := hf
  obtain ⟨b, b', hb, hb', hg⟩ := hg
  have : Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal) :=
    Ring.krullDimLE_one_localization_of_height_eq_one q.1 q.2
  have : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal) :=
    Ring.krullDimLE_one_quotient_of_height_eq_one hA q.1 q.2
  have : IsDedekindDomain (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A)) :=
    Ring.TameSymbol.isDedekindDomain_integralClosure (Localization.AtPrime q.1.asIdeal)
      (FractionRing A) (hfin q.1 q.2)
  have : IsFractionRing (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A))
      (FractionRing A) :=
    Ring.TameSymbol.isFractionRing_integralClosure (Localization.AtPrime q.1.asIdeal)
      (FractionRing A)
  -- an element `t ∈ A ∖ q` is a unit in `A_q`, hence has valuation `1` at every `v`.
  have hunit : ∀ (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A))) (t : A),
      t ∉ q.1.asIdeal →
      IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v
        (algebraMap A (FractionRing A) t) = 1 := by
    intro v t ht
    rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime q.1.asIdeal) (FractionRing A)]
    exact Ring.TameSymbol.valuation_unit_eq_one (Localization.AtPrime q.1.asIdeal) v
      (IsLocalization.map_units (Localization.AtPrime q.1.asIdeal)
        (⟨t, ht⟩ : q.1.asIdeal.primeCompl)).unit
  -- `h · c′ = c` and `v(c) = v(c′) = 1 ⇒ v(h) = 1`.
  have hval : ∀ (v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A)))
      (h : (FractionRing A)ˣ) (c c' : A), c ∉ q.1.asIdeal → c' ∉ q.1.asIdeal →
      (h : FractionRing A) * algebraMap A (FractionRing A) c' = algebraMap A (FractionRing A) c →
      IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v (h : FractionRing A) = 1 := by
    intro v h c c' hc hc' hh
    have := congrArg (IsDedekindDomain.HeightOneSpectrum.valuation (FractionRing A) v) hh
    rwa [map_mul, hunit v c hc, hunit v c' hc', mul_one] at this
  -- unfold `tameOrd`; every local factor of the tame symbol is `1`.
  show Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
      (Ring.tameSymbol (Localization.AtPrime q.1.asIdeal) (hfin q.1 q.2) f g) = 1
  suffices hsym : Ring.tameSymbol (Localization.AtPrime q.1.asIdeal) (hfin q.1 q.2) f g = 1 by
    rw [hsym, map_one]
  unfold Ring.tameSymbol Ring.tameSymbolAt
  exact finprod_eq_one_of_forall_eq_one fun v => Ring.TameSymbol.localFactor_eq_one _ v f g
    (hval v f a a' ha ha' hf) (hval v g b b' hb hb' hg)
