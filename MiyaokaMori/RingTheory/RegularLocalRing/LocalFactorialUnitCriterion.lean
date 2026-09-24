import MiyaokaMori.Prelude
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # The unit criterion in a local factorial ring

The criterion "a unit at all height-one primes ⇒ a unit" in a local factorial ring (the injectivity half of
Hartshorne II.6.11, and the algebraic fact actually used in the gluing step of II.6.2), **without algebraic
Hartogs** (Hartshorne II.6.3A): only reduced fractions `a/b` in a UFD
(`UniqueFactorizationMonoid.exists_reduced_factors`) and Krull's principal ideal theorem
(`Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors`) are used.

Reference: Hartshorne, *Algebraic Geometry*, Prop. II.6.11 (p. 141), end of the first paragraph of the proof
("the Weil divisor of `f_i` on `U_i` is `0` ⇒ `f_i ∈ Γ(U_i, O^*)`"); here written as a purely algebraic
statement about the localization `B = A_𝔪`, with the standard UFD argument (the converse direction of "height-one
primes of a UFD are principal" in the proof of Matsumura, *Commutative Ring Theory*, Thm 20.1), without the
Hartogs lemma for Noetherian normal domains.

Also a small lemma: on a DVR, `ordFrac x = 1 ⇒ x` is the image of a unit (the valuation characterization of
Stacks 02MD). ("A regular local ring of dimension `1` is a DVR" is
`MiyaokaMori.RingTheory.isDiscreteValuationRing_of_regularLocalRing_dimension_one`, Stacks 00PD.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

noncomputable section

/-- An element of the fraction field of a DVR with `ordFrac x = 1` (i.e. valuation `0`) is the image of a unit of
`R`. Proof: `Ring.associated_of_ordFrac_eq x 1` gives `u • x = 1`, so `x = algebraMap u⁻¹`. -/
theorem Ring.exists_units_algebraMap_eq_of_ordFrac_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] {x : K}
    (hx : Ring.ordFrac R x = 1) : ∃ u : Rˣ, algebraMap R K u = x := by
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := R) (K := K) x 1 (by rw [hx, map_one])
  have h1 : algebraMap R K u * x = 1 := by
    rwa [Units.smul_def, Algebra.smul_def] at hu
  have h2 : algebraMap R K (u⁻¹ : Rˣ) * algebraMap R K u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨u⁻¹, ?_⟩
  calc algebraMap R K (u⁻¹ : Rˣ)
      = algebraMap R K (u⁻¹ : Rˣ) * (algebraMap R K u * x) := by rw [h1, mul_one]
    _ = x := by rw [← mul_assoc, h2, one_mul]

namespace IsLocalization.AtPrime

/-- The core step. `B` is a Noetherian UFD, `B = A_𝔪`. Let `x, y ∈ B` be coprime with `x ≠ 0`, and suppose that
for every height-one prime `p` of `A` there are `u, s ∈ A ∖ p` with `s·x = u·y`. Then `x` is a unit.

Proof: suppose `x` is not a unit and take a prime factor `π ∣ x` (`WfDvdMonoid.exists_irreducible_factor`;
irreducible = prime in a UFD). `q := (π)` is a prime of `B` of height `1` (Krull's principal ideal theorem;
`π` a nonunit nonzerodivisor); `p := q ∩ A` is a prime of `A` of height `1` (`IsLocalization.height_under`:
localization preserves heights of primes). So there are `u, s ∉ p` with `s·x = u·y`. `π ∣ x ∣ u·y`, hence
`π ∣ u` or `π ∣ y`: the former says `u ∈ q ∩ A = p`, a contradiction; the latter contradicts coprimality of
`x, y` (`π ∣ x` and `π ∣ y` ⇒ `π` a unit). -/
theorem isUnit_of_isRelPrime_of_forall_height_one
    {A : Type u} [CommRing A] [IsDomain A] (m : Ideal A) [m.IsPrime]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] [IsLocalization.AtPrime B m]
    [IsNoetherianRing B] [UniqueFactorizationMonoid B]
    {x y : B} (hxy : IsRelPrime x y) (hx0 : x ≠ 0)
    (h : ∀ p : Ideal A, p.IsPrime → p.height = 1 →
      ∃ u s : A, u ∉ p ∧ s ∉ p ∧ algebraMap A B s * x = algebraMap A B u * y) :
    IsUnit x := by
  by_contra hx
  obtain ⟨π, hπirr, hπx⟩ := WfDvdMonoid.exists_irreducible_factor hx hx0
  have hπ : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr
  let q : Ideal B := Ideal.span {π}
  have hq : q.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have hqh : q.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) hπirr.not_isUnit
  let p : Ideal A := q.under A
  have hp : p.IsPrime := Ideal.IsPrime.under A q
  have hph : p.height = 1 := (IsLocalization.height_under m.primeCompl q).trans hqh
  obtain ⟨u, s, hu, hs, heq⟩ := h p hp hph
  have hdvd : π ∣ algebraMap A B u * y := by
    rw [← heq]
    exact Dvd.dvd.mul_left hπx _
  rcases hπ.dvd_or_dvd hdvd with hdu | hdy
  · apply hu
    show algebraMap A B u ∈ q
    exact Ideal.mem_span_singleton.mpr hdu
  · exact hπirr.not_isUnit (hxy hπx hdy)

/-- **The unit criterion in a local factorial ring** (the algebraic core of the injectivity half of Hartshorne
II.6.11, without Hartogs).

`A` a domain, `K` its fraction field, `𝔪` a prime, `B = A_𝔪` a Noetherian UFD (e.g. a regular local ring),
`f ∈ K^×`. If for every height-one prime `p` of `A`, `f` is a unit in `A_p` (written: there are `u, s ∈ A ∖ p`
with `s·f = u`), then `f` is the image of a unit of `B`.

Proof: `K` is also the fraction field of `B`; write `f = a/b` and cancel common factors to get `f = a'/b'` with
`a', b'` coprime and nonzero (`UniqueFactorizationMonoid.exists_reduced_factors`). `s·f = u` becomes the
equation `s·a' = u·b'` in `B`; the previous lemma applied to `a'` gives that `a'` is a unit; reading the
equation as `u·b' = s·a'` and applying it to `b'` gives that `b'` is a unit. Hence `f = a'·b'⁻¹` is the image
of a unit. -/
theorem exists_units_algebraMap_eq_of_forall_height_one
    {A : Type u} [CommRing A] [IsDomain A]
    {K : Type w} [Field K] [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) [m.IsPrime]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] [IsLocalization.AtPrime B m]
    [IsNoetherianRing B] [UniqueFactorizationMonoid B]
    [Algebra B K] [IsScalarTower A B K]
    {f : K} (hf : f ≠ 0)
    (h1 : ∀ p : Ideal A, p.IsPrime → p.height = 1 →
      ∃ u s : A, u ∉ p ∧ s ∉ p ∧ algebraMap A K s * f = algebraMap A K u) :
    ∃ b : Bˣ, algebraMap B K b = f := by
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl B K
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  obtain ⟨a, b, hb, hfab⟩ := IsFractionRing.div_surjective (A := B) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hf
    rw [← hfab, map_zero, zero_div]
  obtain ⟨a', b', c', hcop, hca, hcb⟩ := UniqueFactorizationMonoid.exists_reduced_factors a ha0 b
  have hc0 : c' ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hcb, zero_mul])
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    exact ha0 (by rw [← hca, mul_zero])
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hcb, mul_zero])
  have hcK : algebraMap B K c' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc0
  have hb'K : algebraMap B K b' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb'0
  -- f = a'/b'
  have hf' : f = algebraMap B K a' / algebraMap B K b' := by
    rw [← hfab, ← hca, ← hcb, map_mul, map_mul, mul_div_mul_left _ _ hcK]
  -- the equation `s·f = u` in `K` becomes `s·a' = u·b'` in `B`
  have hB : ∀ u s : A, algebraMap A K s * f = algebraMap A K u →
      algebraMap A B s * a' = algebraMap A B u * b' := by
    intro u s hus
    apply hinj
    rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [hf', mul_div_assoc', div_eq_iff hb'K] at hus
    exact hus
  have hua : IsUnit a' :=
    isUnit_of_isRelPrime_of_forall_height_one m B hcop ha'0 (fun p hp hph => by
      obtain ⟨u, s, hu, hs, hus⟩ := h1 p hp hph
      exact ⟨u, s, hu, hs, hB u s hus⟩)
  have hub : IsUnit b' :=
    isUnit_of_isRelPrime_of_forall_height_one m B hcop.symm hb'0 (fun p hp hph => by
      obtain ⟨u, s, hu, hs, hus⟩ := h1 p hp hph
      exact ⟨s, u, hs, hu, (hB u s hus).symm⟩)
  obtain ⟨ua, rfl⟩ := hua
  obtain ⟨ub, rfl⟩ := hub
  refine ⟨ua * ub⁻¹, ?_⟩
  rw [hf', Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv]

end IsLocalization.AtPrime

end
