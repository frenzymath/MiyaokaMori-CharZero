import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Ramification and the canonical orders of discrete valuation rings

This is the local algebra used in the proof of Proposition 3.2 of the paper. The ramification
index is Mathlib's actual local module length, `Ideal.ramificationIdx`; the field
valuations and `Ring.ordFrac` are Mathlib's canonical ones. No numerical index or
formula for arbitrary field elements is assumed as input.

The local DVR results need an injective local homomorphism and compatible fraction
field maps. They do not require the target DVR to be finite over the source DVR.
The fundamental sum is a separate result for an actual finite algebra. Applying
these results to a curve morphism still requires the stalk/function-field commuting
square for that same morphism, and the geometric DVR properties of its stalks.

Sources: Stacks Project tags 09E4, 09E5, 09E8, 00PD and 02MD. The first two results
reuse individually selected, admission-free proofs from the historical
`KummerRamificationData` module; this module has no historical imports.
-/

noncomputable section

open IsDedekindDomain

namespace MiyaokaMori.RingTheory.DVRRamification

section DedekindExtension

variable {R S K L : Type*}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]

/-- Adic valuations scale by the actual local ramification index. -/
theorem valuation_liesOver_eq_ramification (p : HeightOneSpectrum R)
    (q : HeightOneSpectrum S) [q.asIdeal.LiesOver p.asIdeal] (a : K) :
    p.valuation K a ^ q.asIdeal.ramificationIdx R =
      q.valuation L (algebraMap K L a) := by
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal q.asIdeal p.ne_bot]
  exact p.valuation_liesOver L q a

omit [IsDedekindDomain S] in
/-- The sum of actual local indices times residue degrees is the fraction-field degree. -/
theorem fundamental_ramification_sum (p : HeightOneSpectrum R)
    [Module.Finite R S] [Fintype (p.asIdeal.primesOver S)] :
    ∑ q : p.asIdeal.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank K L := by
  rw [IsFractionRing.finrank_eq R K S L]
  exact Ideal.sum_ramification_inertia_eq_finrank p.asIdeal S

end DedekindExtension

section LocalDVR

variable {R S : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- A local homomorphism between DVRs carries the target maximal ideal over the source one. -/
theorem maximalIdeal_liesOver :
    (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
  ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩

/-- An injective local map of DVRs has strictly positive actual ramification index. -/
theorem ramificationIdx_pos (hinj : Function.Injective (algebraMap R S)) :
    0 < (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    maximalIdeal_liesOver
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
    (IsDiscreteValuationRing.not_a_field R)]
  exact Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      (IsLocalRing.maximalIdeal S) (IsDiscreteValuationRing.not_a_field R))

variable {K L : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]

/-- The canonical fraction-field orders scale by the actual DVR ramification index. -/
theorem ordFrac_algebraMap (hinj : Function.Injective (algebraMap R S)) (a : K) :
    Ring.ordFrac S (algebraMap K L a) =
      (Ring.ordFrac R a) ^ (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hlies : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    maximalIdeal_liesOver
  have : ((IsDiscreteValuationRing.maximalIdeal S).asIdeal).LiesOver
      ((IsDiscreteValuationRing.maximalIdeal R).asIdeal) := hlies
  rw [Ring.ordFrac_eq_valuation_inv, Ring.ordFrac_eq_valuation_inv,
    ← valuation_liesOver_eq_ramification
      (IsDiscreteValuationRing.maximalIdeal R) (IsDiscreteValuationRing.maximalIdeal S),
    inv_pow]
  rfl

include K in
/-- The actual ramification index is the order of the image of any source uniformizer. -/
theorem ordFrac_algebraMap_irreducible
    (hinj : Function.Injective (algebraMap R S)) {a : R} (ha : Irreducible a) :
    Ring.ordFrac S (algebraMap R L a) =
      WithZero.exp ((IsLocalRing.maximalIdeal S).ramificationIdx R : ℤ) := by
  rw [IsScalarTower.algebraMap_apply R K L, ordFrac_algebraMap hinj,
    Ring.ordFrac_irreducible ha, ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_one]

end LocalDVR

end MiyaokaMori.RingTheory.DVRRamification
