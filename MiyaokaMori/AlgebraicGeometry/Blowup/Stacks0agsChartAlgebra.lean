import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.RingTheory.RegularLocalRing.RegularLocalDimLeTwoUFD

/-! # The algebra behind `Γ(Bl_𝔪 Spec A, O) = A`

Pure commutative algebra for Stacks 0AGS(4) with `n = 0`
(`AlgebraicGeometry.blowup_regularLocalRing_dimTwo_sections`). `A[J/a] := Ideal.affineBlowup J a` is
the affine blowup algebra, a subalgebra of `Localization.Away a`.

* `Ideal.affineBlowup_exists_pow_mul_eq_algebraMap`: every `f ∈ A[J/a]` satisfies `aⁿ f = b` for some
  `n` and `b ∈ A`;
* `Ideal.affineBlowup_eq_of_algebraMap_pow_mul_eq`: `aⁿ` cancels in `A[J/a]`;
* `Ideal.affineBlowup_eq_algebraMap_of_apply_eq`: if `ρ : A[J/a] → R'` restricts to an injective
  `φ : A → R'` and `ρ f = φ c`, then `f = c` (used to see that a global section which is a constant on
  one chart is the same constant on every other chart);
* `Ideal.affineBlowup_exists_eq_algebraMap_of_prime`: the "`A[J/x] ∩ A[J/y] = A`" step: if `A` is a
  domain, `x` is prime, `x ∤ y`, and `f ∈ A[J/x]`, `g ∈ A[J/y]` become equal in an `A`-algebra `R'` into
  which `A` injects, then `f = g = c` for some `c ∈ A`;
* `Ideal.affineBlowup_algebraMap_injective`, `Ideal.affineBlowup_subsingleton_of_eq_zero`: `A → A[J/a]`
  is injective for `a ≠ 0` (`A` a domain), and `A[J/0] = 0`;
* `IsRegularLocalRing.exists_span_pair_prime_not_dvd`: a two-dimensional regular local ring has
  `𝔪 = (x, y)` with `x` prime and `x ∤ y`.

Source: Stacks 0AGS, proof of (4) (fourth paragraph): "`A[𝔪/x] ∩ A[𝔪/y] = A` because `A` is a UFD
(regular local ring of dimension 2) and `x`, `y` are non-associated primes".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace Ideal

variable {A : Type u} [CommRing A]

/-- Every element `f` of the affine blowup algebra `A[J/a] ⊆ A_a` is a fraction: `aⁿ · f = b` for some
`n : ℕ` and `b ∈ A` (`IsLocalization.surj` for the powers of `a`). -/
theorem affineBlowup_exists_pow_mul_eq_algebraMap (J : Ideal A) (a : A) (f : J.affineBlowup a) :
    ∃ (n : ℕ) (b : A),
      algebraMap A (J.affineBlowup a) (a ^ n) * f = algebraMap A (J.affineBlowup a) b := by
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers a) (f : Localization.Away a)
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, b, Subtype.ext ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  rw [mul_comm, ← hs]
  simp only at hn
  rw [hn]

/-- `aⁿ` cancels in `A[J/a] ⊆ A_a`: `aⁿ f = aⁿ g → f = g`. -/
theorem affineBlowup_eq_of_algebraMap_pow_mul_eq (J : Ideal A) (a : A) (n : ℕ)
    {f g : J.affineBlowup a}
    (h : algebraMap A (J.affineBlowup a) (a ^ n) * f =
      algebraMap A (J.affineBlowup a) (a ^ n) * g) : f = g := by
  apply Subtype.ext
  have hu : IsUnit (algebraMap A (Localization.Away a) (a ^ n)) :=
    IsLocalization.map_units (Localization.Away a) (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)
  have h' := congrArg Subtype.val h
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at h'
  exact hu.mul_left_cancel h'

/-- If a ring map `ρ : A[J/a] → R'` restricts on `A` to an injective `φ : A → R'`, then an element
`f ∈ A[J/a]` with `ρ f = φ c` (`c ∈ A`) is the constant `c`: write `aⁿ f = b`, then
`φ b = φ (aⁿ) · ρ f = φ (aⁿ c)`, so `b = aⁿ c` and `f = c` after cancelling `aⁿ`. -/
theorem affineBlowup_eq_algebraMap_of_apply_eq {R' : Type*} [CommRing R'] (J : Ideal A) (a : A)
    (φ : A →+* R') (hφ : Function.Injective φ) (ρ : J.affineBlowup a →+* R')
    (hρ : ρ.comp (algebraMap A (J.affineBlowup a)) = φ) (f : J.affineBlowup a) (c : A)
    (h : ρ f = φ c) : f = algebraMap A (J.affineBlowup a) c := by
  obtain ⟨n, b, hb⟩ := affineBlowup_exists_pow_mul_eq_algebraMap J a f
  have hφ' : ∀ r : A, ρ (algebraMap A (J.affineBlowup a) r) = φ r := fun r => by
    rw [← hρ, RingHom.comp_apply]
  have h1 : φ b = φ (a ^ n * c) := by
    rw [← hφ' b, ← hb, map_mul, hφ', h, map_mul]
  have h2 : b = a ^ n * c := hφ h1
  apply affineBlowup_eq_of_algebraMap_pow_mul_eq J a n
  rw [hb, h2, map_mul]

/-- **`A[J/x] ∩ A[J/y] = A`.** `A` a domain, `x` a prime element, `x ∤ y`. If `f ∈ A[J/x]` and
`g ∈ A[J/y]` have the same image in an `A`-algebra `R'` (through ring maps `ρₓ`, `ρ_y` restricting to
the same injective `φ : A → R'`), then `f = g = c` for some `c ∈ A`.

Proof: `xⁿ f = a`, `yᵐ g = b` with `a, b ∈ A`; applying `ρₓ`, `ρ_y` and using `ρₓ f = ρ_y g` gives
`φ (yᵐ a) = φ (xⁿ b)`, so `yᵐ a = xⁿ b` in `A`. As `x` is prime and `x ∤ y`, `x ∤ yᵐ`, hence
`xⁿ ∣ a` (`Prime.pow_dvd_of_dvd_mul_left`): `a = xⁿ c`. Cancelling `xⁿ` (in `A_x`) gives `f = c`;
cancelling `xⁿ` in the domain `A` gives `b = yᵐ c`, and cancelling `yᵐ` in `A_y` gives `g = c`. -/
theorem affineBlowup_exists_eq_algebraMap_of_prime [IsDomain A] {R' : Type*} [CommRing R']
    (J : Ideal A) {x y : A} (hx : Prime x) (hxy : ¬ x ∣ y)
    (φ : A →+* R') (hφ : Function.Injective φ)
    (ρx : J.affineBlowup x →+* R') (hρx : ρx.comp (algebraMap A (J.affineBlowup x)) = φ)
    (ρy : J.affineBlowup y →+* R') (hρy : ρy.comp (algebraMap A (J.affineBlowup y)) = φ)
    (f : J.affineBlowup x) (g : J.affineBlowup y) (h : ρx f = ρy g) :
    ∃ c : A, f = algebraMap A (J.affineBlowup x) c ∧ g = algebraMap A (J.affineBlowup y) c := by
  obtain ⟨n, a, ha⟩ := affineBlowup_exists_pow_mul_eq_algebraMap J x f
  obtain ⟨m, b, hb⟩ := affineBlowup_exists_pow_mul_eq_algebraMap J y g
  have hφx : ∀ r : A, ρx (algebraMap A (J.affineBlowup x) r) = φ r := fun r => by
    rw [← hρx, RingHom.comp_apply]
  have hφy : ∀ r : A, ρy (algebraMap A (J.affineBlowup y) r) = φ r := fun r => by
    rw [← hρy, RingHom.comp_apply]
  -- `yᵐ a = xⁿ b` in `A`
  have key : y ^ m * a = x ^ n * b := by
    apply hφ
    rw [map_mul, map_mul, ← hφx a, ← hφy b, ← ha, ← hb, map_mul, map_mul, hφx, hφy, h]
    ring
  have hxym : ¬ x ∣ y ^ m := fun hd => hxy (hx.dvd_of_dvd_pow hd)
  obtain ⟨c, hc⟩ : x ^ n ∣ a := hx.pow_dvd_of_dvd_mul_left n hxym ⟨b, key⟩
  refine ⟨c, ?_, ?_⟩
  · apply affineBlowup_eq_of_algebraMap_pow_mul_eq J x n
    rw [ha, hc, map_mul]
  · have hb' : b = y ^ m * c := by
      have hxn : x ^ n ≠ 0 := pow_ne_zero n hx.ne_zero
      apply mul_left_cancel₀ hxn
      rw [← key, hc]
      ring
    apply affineBlowup_eq_of_algebraMap_pow_mul_eq J y m
    rw [hb, hb', map_mul]

/-- `A → A[J/a]` is injective when `A` is a domain and `a ≠ 0` (it is the corestriction of
`A → A_a`, injective as the powers of `a` are non-zero-divisors). -/
theorem affineBlowup_algebraMap_injective [IsDomain A] (J : Ideal A) {a : A} (ha : a ≠ 0) :
    Function.Injective (algebraMap A (J.affineBlowup a)) := by
  intro r r' h
  have h' := congrArg Subtype.val h
  simp only [Subalgebra.coe_algebraMap] at h'
  exact IsLocalization.injective (Localization.Away a)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha) h'

/-- `A[J/a]` is the zero ring when `a = 0` (it sits inside `A_0 = 0`). -/
theorem affineBlowup_subsingleton_of_eq_zero (J : Ideal A) {a : A} (ha : a = 0) :
    Subsingleton (J.affineBlowup a) := by
  subst ha
  have : Subsingleton (Localization.Away (0 : A)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : A)) ⟨1, pow_one 0⟩
  exact ⟨fun f g => Subtype.ext (Subsingleton.elim _ _)⟩

end Ideal

/-- **Regular system of parameters of a two-dimensional regular local ring, with primality.** If `A` is
regular local of dimension `2`, then `𝔪 = (x, y)` with `x` a prime element and `x ∤ y`.

Proof. `spanFinrank 𝔪 = 2` (definition of `IsRegularLocalRing`), so `𝔪 = span {x, y}` for a two-element
set (`Submodule.FG.exists_span_finset_card_eq_spanFinrank`, `Finset.card_eq_two`). If `x ∣ y` then
`𝔪 = (x)` and `spanFinrank 𝔪 ≤ 1`; if `x ∈ 𝔪²` then `𝔪 ≤ (y) + 𝔪·𝔪`, so `𝔪 ≤ (y)` by Nakayama
(`Submodule.le_of_le_smul_of_le_jacobson_bot`) and again `spanFinrank 𝔪 ≤ 1`; both contradict
`spanFinrank 𝔪 = 2`. Hence `x ∉ 𝔪²`, which makes `x` irreducible (a factorisation into two non-units
lands in `𝔪·𝔪 = 𝔪²`), and irreducible elements are prime in the UFD `A`
(`IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two`). -/
theorem IsRegularLocalRing.exists_span_pair_prime_not_dvd (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    ∃ x y : A, Ideal.span {x, y} = IsLocalRing.maximalIdeal A ∧ Prime x ∧ ¬ x ∣ y := by
  classical
  have hufd : UniqueFactorizationMonoid A :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two A (hdim ▸ le_rfl)
  have hrank : (IsLocalRing.maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨s, hs, hspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A)).exists_span_finset_card_eq_spanFinrank
  rw [hrank] at hs
  obtain ⟨x, y, -, rfl⟩ := Finset.card_eq_two.mp hs
  rw [Finset.coe_pair] at hspan
  have hx : x ∈ IsLocalRing.maximalIdeal A := hspan ▸ Ideal.subset_span (by simp)
  have hy : y ∈ IsLocalRing.maximalIdeal A := hspan ▸ Ideal.subset_span (by simp)
  -- `𝔪` is not generated by a single element
  have hnot1 : ∀ z : A, IsLocalRing.maximalIdeal A ≠ Ideal.span {z} := by
    intro z hz
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (M := A) (s := {z})
      (Set.finite_singleton z)
    rw [← Ideal.span, ← hz, hrank, Set.ncard_singleton] at h1
    omega
  -- `x ∤ y`
  have hxy : ¬ x ∣ y := by
    rintro ⟨c, rfl⟩
    apply hnot1 x
    rw [← hspan, Submodule.span_insert]
    exact sup_eq_left.mpr (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right x c))
  -- `x ∉ 𝔪²` (Nakayama)
  have hx2 : x ∉ IsLocalRing.maximalIdeal A ^ 2 := by
    intro hx2
    apply hnot1 y
    apply le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy))
    have hfg : (IsLocalRing.maximalIdeal A).FG := IsNoetherian.noetherian _
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rw [Ideal.smul_eq_mul, ← sq]
    intro z hz
    rw [← hspan] at hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.smul_mem _ a hx2))
      (Submodule.mem_sup_left (Submodule.smul_mem _ b (Submodule.mem_span_singleton_self y)))
  -- `x` is irreducible, hence prime in the UFD `A`
  have hirr : Irreducible x := by
    refine irreducible_iff.mpr ⟨fun hu => ?_, fun a b hab => ?_⟩
    · exact (IsLocalRing.mem_maximalIdeal x).mp hx hu
    · by_contra hne
      rw [not_or] at hne
      apply hx2
      rw [hab, sq]
      exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal a).mpr hne.1)
        ((IsLocalRing.mem_maximalIdeal b).mpr hne.2)
  exact ⟨x, y, hspan, UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr, hxy⟩

end
