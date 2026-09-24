import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameSymbol
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteCodimOnePointsOutsideOpen
import MiyaokaMori.RingTheory.OrderOfVanishing.Stacks02mj
import MiyaokaMori.RingTheory.KeyLemma.TameOrd
import MiyaokaMori.RingTheory.KeyLemma.TameOrdEqOne
import MiyaokaMori.RingTheory.KeyLemma.HeightOnePrimesFinite
import MiyaokaMori.RingTheory.KeyLemma.BimulReduction
import MiyaokaMori.RingTheory.KeyLemma.Stacks0eaw

/-! # Stacks 0EAX: the Key Lemma (Milnor–Gersten vanishing in low degree)

Stacks 0EAX: `A` a two-dimensional Noetherian local domain, `K = Frac A`, `f, g ∈ K^*`; then
`Σ_{ht q = 1} ord_{A/q}(∂_{A_q}(f, g)) = 0` (only finitely many terms are nonzero). Stated here under the
assumption that the normalization of `A` is finite over `A` (so that the definition of the tame symbol via
the normalization agrees with the `∂` of Stacks).

Reference: Stacks 0EAX (chow-lemma-milnor-gersten-low-degree); the proof goes through 0EAW
(chow-lemma-key-nonzerodivisors), using 0EAG, 0EAV, 0EAT, 0EA9, 0EAC, 0EAB, 02QF, 02MJ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Stacks 0EAX (Milnor–Gersten vanishing in low degree, the Key Lemma): `A` a two-dimensional Noetherian
   local domain, `K = Frac A`, `f, g ∈ K^*`. For every height-one prime `q`: `A_q` is a one-dimensional
   Noetherian local domain with fraction field `K`; `∂_{A_q}(f, g) ∈ κ(q) = q.ResidueField = Frac(A/q)`
   (the tame symbol); `ord_{A/q}` is Mathlib's `Ring.ordFrac (A ⧸ q)` (`A/q` a one-dimensional
   Noetherian local domain, the length definition of 02MD). The conclusion is stated as: only finitely
   many `q` contribute (`Function.mulSupport` finite), and `∏ᶠ_q ord_{A/q}(∂_{A_q}(f,g)) = 1`
   (multiplicative notation in `ℤᵐ⁰`, i.e. `Σ = 0`). The hypothesis `hfin` (the normalization of `A` is
   finite over `A`, e.g. `A` a localization of a finite type algebra over a field) guarantees that the
   normalization `(Ã)_q` of each `A_q` is finite over `A_q`, so that the definition of the tame symbol
   via the normalization agrees with `∂_{A_q}` of Stacks 0EAQ (Stacks 0EAX itself has no such
   assumption).

   The two dimension lemmas `Ring.krullDimLE_one_localization_of_height_eq_one`,
   `Ring.krullDimLE_one_quotient_of_height_eq_one` live in `KeyLemma/TameOrd.lean` and are visible here
   through the imports. -/

/-- Finite support: `f = a/a′`, `g = b/b′`, `t = aa′bb′ ≠ 0`; at the height-one primes not containing `t`,
`f` and `g` are units and the term is `1`. -/
theorem Ring.tameOrd_mulSupport_finite (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (f g : (FractionRing A)ˣ) :
    (Function.mulSupport fun q : {q : PrimeSpectrum A // q.asIdeal.height = 1} =>
      Ring.tameOrd A hA hfin q f g).Finite := by
  obtain ⟨a, a', ha', hfa⟩ := IsFractionRing.div_surjective (A := A) (f : FractionRing A)
  obtain ⟨b, b', hb', hgb⟩ := IsFractionRing.div_surjective (A := A) (g : FractionRing A)
  have hinj := IsFractionRing.injective A (FractionRing A)
  have ha'0 : a' ≠ 0 := nonZeroDivisors.ne_zero ha'
  have hb'0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  have ha'K : algebraMap A (FractionRing A) a' ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha'0
  have hb'K : algebraMap A (FractionRing A) b' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb'0
  have hfa' : (f : FractionRing A) * algebraMap A (FractionRing A) a' = algebraMap A (FractionRing A) a := by
    rw [← hfa, div_mul_cancel₀ _ ha'K]
  have hgb' : (g : FractionRing A) * algebraMap A (FractionRing A) b' = algebraMap A (FractionRing A) b := by
    rw [← hgb, div_mul_cancel₀ _ hb'K]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfa'
    exact (mul_ne_zero f.ne_zero ha'K) hfa'
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hgb'
    exact (mul_ne_zero g.ne_zero hb'K) hgb'
  have ht : a * a' * (b * b') ≠ 0 := mul_ne_zero (mul_ne_zero ha0 ha'0) (mul_ne_zero hb0 hb'0)
  refine ((PrimeSpectrum.finite_height_one_mem ht).preimage
    (Subtype.val_injective.injOn)).subset fun q hq => ?_
  refine ⟨q.2, ?_⟩
  by_contra hcon
  refine hq (Ring.tameOrd_eq_one_of_not_mem A hA hfin q f g
    ⟨a, a', fun h => hcon ?_, fun h => hcon ?_, hfa'⟩ ⟨b, b', fun h => hcon ?_, fun h => hcon ?_, hgb'⟩)
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h)
  · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ h)
  · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h)

/-- Stacks 0EAX.

The hypothesis `hfin` is the finiteness of the normalization of each `A_q` (required by the signature of
`Ring.tameSymbol`, where it replaces Krull–Akizuki, see `Ring.TameSymbol.isDedekindDomain_integralClosure`);
the tame symbol `∂` is taken on **`A_q`**, not on `A`, so what is needed is `Module.Finite A_q ((A_q)~)` at
every height-one prime `q`. The hypothesis `hB : Module.Finite A (integralClosure A (FractionRing A))`
(finiteness of the normalization of `A` itself) is needed because the first paragraph of Stacks 0EAW
requires a **global** finite extension `A ⊂ B` on which `a, b` have local factorizations at every
`B_{q_i}`; the original builds it pointwise with 0EAG + 0EAV and glues, here we take `B = Ã` directly.
`hB` implies `hfin` (integral closure commutes with localization, Stacks 0307), but not conversely; in
the geometric application (0AYC, `A = O_{X,ξ}`, `X` locally of finite type over a field) both come from
the Nagata property. Both hypotheses are kept side by side.

The proof assembles `Ring.tameOrd_mulSupport_finite` (from `PrimeSpectrum.finite_height_one_mem` and
`Ring.tameOrd_eq_one_of_not_mem`), `KeyLemma.finprod_eq_one_of_bimul` (the bimultiplicative reduction of
the original 0EAX) and `Ring.tameOrd_finprod_eq_one_of_mem` (0EAW). -/
theorem Ring.tameSymbol_milnorGersten_lowDegree (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hB : Module.Finite A (integralClosure A (FractionRing A)))
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (f g : (FractionRing A)ˣ) :
    let F : {q : PrimeSpectrum A // q.asIdeal.height = 1} → WithZero (Multiplicative ℤ) := fun q =>
      letI : Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal) :=
        Ring.krullDimLE_one_localization_of_height_eq_one q.1 q.2
      letI : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal) :=
        Ring.krullDimLE_one_quotient_of_height_eq_one hA q.1 q.2
      Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
        (Ring.tameSymbol (Localization.AtPrime q.1.asIdeal) (hfin q.1 q.2) f g)
    (Function.mulSupport F).Finite ∧ ∏ᶠ q, F q = 1 := by
  intro F
  have hF : F = fun q => Ring.tameOrd A hA hfin q f g := rfl
  rw [hF]
  refine ⟨Ring.tameOrd_mulSupport_finite A hA hfin f g, ?_⟩
  have hinj := IsFractionRing.injective A (FractionRing A)
  refine KeyLemma.finprod_eq_one_of_bimul
    (fun q f g => Ring.tameOrd A hA hfin q f g)
    (fun q f f' g => Ring.tameOrd_mul_left A hA hfin q f f' g)
    (fun q f g g' => Ring.tameOrd_mul_right A hA hfin q f g g')
    (fun f g => Ring.tameOrd_mulSupport_finite A hA hfin f g)
    {s | ∃ (a : A) (ha : a ≠ 0), s = Units.mk0 (algebraMap A (FractionRing A) a)
      ((map_ne_zero_iff _ hinj).mpr ha)} ?_ ?_ f g
  · intro f
    obtain ⟨a, a', ha', hfa⟩ := IsFractionRing.div_surjective (A := A) (f : FractionRing A)
    have ha'0 : a' ≠ 0 := nonZeroDivisors.ne_zero ha'
    have ha'K : algebraMap A (FractionRing A) a' ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha'0
    have hfa' : (f : FractionRing A) * algebraMap A (FractionRing A) a'
        = algebraMap A (FractionRing A) a := by
      rw [← hfa, div_mul_cancel₀ _ ha'K]
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hfa'
      exact (mul_ne_zero f.ne_zero ha'K) hfa'
    exact ⟨_, ⟨a, ha0, rfl⟩, _, ⟨a', ha'0, rfl⟩, Units.ext hfa'⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact Ring.tameOrd_finprod_eq_one_of_mem A hA hB hfin a b ha hb


end
