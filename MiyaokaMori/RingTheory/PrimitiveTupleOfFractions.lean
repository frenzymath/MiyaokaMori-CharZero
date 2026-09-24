import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.PrimitiveTuple

/-! # Primitive tuples from tuples of fractions

Any finite tuple in the fraction field of a UFD `A` that is not identically zero becomes, after
multiplication by a nonzero scalar, a primitive tuple in `A` (clear denominators, divide by the gcd).

References: Debarre, *Higher-Dimensional Algebraic Geometry*, first paragraph of the proof of
Thm 5.18 (writing `π` as `(s_0, …, s_N)`); the step "after removing fixed divisorial components" in
the proof of Theorem 4.2 of the paper; Shafarevich, *Basic Algebraic Geometry 1*,
II.3.1, proof of Thm 2.12 (`f_i ∈ O_x` without common factor).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

noncomputable section

/-- Let `A` be a UFD, `K = Frac A`, and `f : ι → K` (`ι` finite) not identically zero. Then there are
`c ∈ Kˣ` and `a : ι → A` with `f_i = c · a_i` and `a` primitive (no prime element divides all `a_i`).

Proof. (1) Clear denominators: a common denominator `s ∈ A ∖ {0}` with `s · f_i = algebraMap b_i`
(`IsLocalization.exist_integer_multiples_of_finite`).
(2) `b ≠ 0` (otherwise `f = 0`). Let `g := Finset.univ.gcd b` (a UFD is a `NormalizedGCDMonoid`
via `UniqueFactorizationMonoid.toNormalizedGCDMonoid` with
`UniqueFactorizationMonoid.strongNormalizationMonoid`, used as a local `letI`, not as a global
instance); `g ≠ 0` (`Finset.gcd_eq_zero_iff`), `b_i = g · a_i` and `Finset.univ.gcd a = 1`
(`Finset.extract_gcd`).
(3) If a prime `p` divides all `a_i`, then `p ∣ gcd a = 1` (`Finset.dvd_gcd`), so `p` is a unit,
contradicting `Prime.not_unit`.
(4) `c := algebraMap g / algebraMap s ∈ Kˣ` (`g`, `s` nonzero, `IsFractionRing.injective`).
Edge cases: if `A` is a field there are no primes and primitivity is vacuous; if `ι` is empty then
`f ≠ 0` is impossible (the proof derives that `ι` is nonempty from `hf`). -/
theorem exists_primitive_tuple_of_fractions
    {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [Field K] [Algebra A K] [IsFractionRing A K] {ι : Type*} [Fintype ι]
    (f : ι → K) (hf : f ≠ 0) :
    ∃ (c : Kˣ) (a : ι → A), (∀ i, f i = (c : K) * algebraMap A K (a i)) ∧ IsPrimitiveTuple a := by
  classical
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  -- (1) clear denominators
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) f
  choose b hb using hs
  have hs0 : (s : A) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsK : algebraMap A K (s : A) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  -- (2) some f i ≠ 0, hence some b i ≠ 0, and ι is nonempty
  obtain ⟨i₀, hi₀⟩ : ∃ i, f i ≠ 0 := by
    by_contra h
    exact hf (funext fun i => not_not.mp (not_exists.mp h i))
  have hb0 : b i₀ ≠ 0 := by
    intro h0
    have := hb i₀
    rw [h0, map_zero, Algebra.smul_def] at this
    exact hi₀ ((mul_eq_zero.mp this.symm).resolve_left hsK)
  have : Nonempty ι := ⟨i₀⟩
  -- gcd structure on the UFD (local instances only)
  let _ : NormalizationMonoid A := (UniqueFactorizationMonoid.strongNormalizationMonoid (α := A)).toNormalizationMonoid
  let _ : NormalizedGCDMonoid A := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  obtain ⟨a, ha, hgcd⟩ := Finset.extract_gcd b (Finset.univ_nonempty (α := ι))
  set g : A := Finset.univ.gcd b with hg
  have hg0 : g ≠ 0 := by
    intro h0
    rw [hg, Finset.gcd_eq_zero_iff] at h0
    exact hb0 (h0 i₀ (Finset.mem_univ _))
  have hgK : algebraMap A K g ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg0
  -- (4) the scalar
  refine ⟨Units.mk0 (algebraMap A K g / algebraMap A K (s : A)) (div_ne_zero hgK hsK), a, ?_, ?_⟩
  · intro i
    have h1 := hb i
    rw [ha i (Finset.mem_univ _), map_mul, Algebra.smul_def] at h1
    -- h1 : algebraMap g * algebraMap (a i) = algebraMap s * f i
    rw [Units.val_mk0]
    field_simp
    rw [h1]
    ring
  · -- (3) primitivity
    intro p hp
    by_contra h
    have hdvd : p ∣ Finset.univ.gcd a :=
      Finset.dvd_gcd fun i _ => not_not.mp (not_exists.mp h i)
    rw [hgcd] at hdvd
    exact hp.not_isUnit (isUnit_of_dvd_one hdvd)

end
