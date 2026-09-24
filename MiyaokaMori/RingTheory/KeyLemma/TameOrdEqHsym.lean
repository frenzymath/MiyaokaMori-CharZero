import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameOrd
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.SumDefs
import MiyaokaMori.RingTheory.KeyLemma.HsymEqLam
import MiyaokaMori.RingTheory.KeyLemma.TameOrdBridge
import MiyaokaMori.RingTheory.OrderOfVanishing.OrdNormEqLength

/-! # `tameOrd` as a sum of multiplicities `Hsym`

`A` a two-dimensional Noetherian local domain with finite normalization `B = Ã`, `q` a height-one prime,
`a, b ∈ A ∖ 0`. Then
`ord_{A/q}(∂_{A_q}(a, b)) = −Σ_{𝔭 ∈ MinPrimes_B(ab), 𝔭 ∩ A = q} e_A(B/(abB_𝔭 ∩ B), a, b)`.

Reference: the equation `ord_{A/𝔮_i}(∂_{A_{𝔮_i}}(a,b)) = Σ_j ord_{B/𝔮_{i,j}}(∂_{B_{𝔮_{i,j}}}(a,b))` at the
end of the first paragraph of Stacks 0EAW (0EAT + 02MJ), combined with `e_A(M_i, a, b) = −ord(∂(a, b))` of
the third and fourth paragraphs; `ord_{A/q} ∘ Norm = A-length` is Stacks 02MI
(`Ring.ordFrac_norm_eq_exp_length`).

The steps (B1)–(B5) and two auxiliary lemmas are in `TameOrdBridge`; the theorem below assembles them.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open PeriodicComplex

noncomputable section

/-- Proof. This translates the language in which `Ring.tameSymbol` is defined (the `HeightOneSpectrum` of
`integralClosure (Localization.AtPrime q) K`, the residue fields of the valuation subrings, `Algebra.norm`)
into the language of `(A, B = Ã, 𝔭)`, along the route (B1)–(B6):

Write `K = Frac A`, `R = A_q`, `B = integralClosure A K`, `C = integralClosure R K`,
`ι = KeyLemma.toIcAtPrime A q`, `𝔭_v = KeyLemma.primeBelow A q v`, `O_v = (v.valuation K).valuationSubring`.

* (B6a) `KeyLemma.tameOrd_eq_finprod_ordFrac_tameSymbolAt`: `tameOrd` unfolds to
  `∏ᶠ_v ordFrac_{A/q}(tameSymbolAt R v a b)` (`map_finprod` + `finite_mulSupport_localFactor`).
* (B6b) `KeyLemma.ordFrac_tameSymbolAt_eq_exp_neg_Hsym`: the factor at each `v` equals
  `exp(−Hsym A a b 𝔭_v)`; assembled from (B2) symbolic powers ↔ valuation, (B3) finite length, (B4) units
  as fractions, (B5) 02MI and `KeyLemma.Hsym_eq_lam_sub`.
* `KeyLemma.exp_finsum` + `finsum_neg_distrib`: `∏ᶠ exp(−x_v) = exp(−Σᶠ x_v)`.
* (B1′) `KeyLemma.finite_support_Hsym_primeBelow`: the finiteness of support needed in the previous step.
* (B1) `KeyLemma.finsum_Hsym_primeBelow_eq`: re-indexing, replacing the sum over `v` by the sum over
  `{𝔭 ∈ MinPrimes(ab) | 𝔭 ∩ A = q}`.

Edge cases: if `C` has only one maximal ideal over `q`, or `R` is already a DVR (`C = R`), the formula is
unchanged; if `a` or `b` is a unit of `R`, the corresponding `e` or `f` is `0`; for finite or inseparable
residue fields, `Algebra.norm` and 02MI still hold (02MI uses determinants, no separability assumption).

Ingredients: the equality form `integralClosure R K = S⁻¹B` of Stacks 0307 (used in (B1) and (B4)); the
identification `IsFractionRing (B ⧸ 𝔭_v) κ(O_v)` in the form of (B5a) `KeyLemma.exists_residue_div` and
(B5a′) `KeyLemma.residue_toValuationSubringIC_eq_zero_iff`; (B5b) `KeyLemma.length_quotient_base`
(`length_{A/q} = length_A`); the hypotheses `hB`, `hfin` come from the finiteness of the normalization of a
stalk and its localizations. -/
theorem KeyLemma.tameOrd_eq_exp_neg_finsum_Hsym (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1}) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Ring.tameOrd A hA hfin q
        (Units.mk0 (algebraMap A (FractionRing A) a)
          ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha))
        (Units.mk0 (algebraMap A (FractionRing A) b)
          ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hb))
      = WithZero.exp (-(∑ᶠ 𝔭 : {𝔭 : KeyLemma.MinPrimes
            (algebraMap A (integralClosure A (FractionRing A)) a *
              algebraMap A (integralClosure A (FractionRing A)) b) //
            𝔭.1.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A))) = q.1.asIdeal},
          KeyLemma.Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
            (algebraMap A (integralClosure A (FractionRing A)) b) 𝔭.1.1)) := by
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal) :=
    Ring.krullDimLE_one_localization_of_height_eq_one q.1 q.2
  haveI : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal) :=
    Ring.krullDimLE_one_quotient_of_height_eq_one hA q.1 q.2
  letI : IsDedekindDomain
      (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A)) :=
    Ring.TameSymbol.isDedekindDomain_integralClosure (Localization.AtPrime q.1.asIdeal)
      (FractionRing A) (hfin q.1 q.2)
  letI : IsFractionRing (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A))
      (FractionRing A) :=
    Ring.TameSymbol.isFractionRing_integralClosure (Localization.AtPrime q.1.asIdeal)
      (FractionRing A)
  have hsupp : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (Localization.AtPrime q.1.asIdeal) (FractionRing A)) =>
      -(KeyLemma.Hsym A (algebraMap A (integralClosure A (FractionRing A)) a)
        (algebraMap A (integralClosure A (FractionRing A)) b)
        (KeyLemma.primeBelow A q.1 v))).Finite := by
    refine (KeyLemma.finite_support_Hsym_primeBelow q.1 (hfin q.1 q.2) a b ha hb).subset ?_
    intro v hv
    simp only [Function.mem_support, ne_eq, neg_eq_zero] at hv ⊢
    exact hv
  rw [KeyLemma.tameOrd_eq_finprod_ordFrac_tameSymbolAt hA hfin q,
    finprod_congr (fun v => KeyLemma.ordFrac_tameSymbolAt_eq_exp_neg_Hsym hA q hB
      (hfin q.1 q.2) a b ha hb v),
    ← KeyLemma.exp_finsum _ hsupp, finsum_neg_distrib,
    KeyLemma.finsum_Hsym_primeBelow_eq q.1 hB (hfin q.1 q.2) q.2 hA a b ha hb]

end
