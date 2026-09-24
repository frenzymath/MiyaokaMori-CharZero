import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.OrderOfVanishing.OrdNormEqLength
import MiyaokaMori.RingTheory.Length.LengthSumInertia

/-! # Stacks 02MJ: the order of a norm as a weighted sum of orders

Stacks 02MJ: `A` a one-dimensional Noetherian local domain, `A ⊂ B` a finite extension of domains, `L/K` the
extension of fraction fields, **`y ∈ L^*`**; then
`ord_A(Nm_{L/K} y) = Σ_{maximal ideals m_i of B} [κ(m_i):κ(m_A)]·ord_{B_{m_i}}(y)` (the order of vanishing
of the norm is the sum of the orders at the points above, weighted by residue degrees).

This file first proves the case `y ∈ B ∖ 0` (`Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord`) and then extends
it by division to `y ∈ L^*` (`Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord_of_eq_div`: `y = b/b'`, and
`ord_{B_m}` on the right becomes `ord_{B_m}(b) − ord_{B_m}(b')`; every element of `L^*` can be so written,
`IsFractionRing.div_surjective`). Users that only need the step "both sides multiplicative in `y` + equal on
`B ∖ 0` ⇒ equal on `L^*`" (as 02RT does) can use `Ring.eq_of_mul_of_eq_on_algebraMap` directly.

Reference: Stacks 02MJ (used in Stacks 02R5/02RM/02RH/02RT/02S2).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The maximal ideals of a finite `A`-algebra (`A` local) all lie over `m_A`. -/
theorem Ring.liesOver_maximalIdeal_of_finite {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (m : MaximalSpectrum B) :
    m.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hmax : (m.asIdeal.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m.asIdeal
  exact ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩

theorem Ring.finite_maximalSpectrum_of_finite {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] : Finite (MaximalSpectrum B) := by
  have hfin : ((IsLocalRing.maximalIdeal A).primesOver B).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  have := hfin.to_subtype
  let g : MaximalSpectrum B → (IsLocalRing.maximalIdeal A).primesOver B := fun m =>
    ⟨m.asIdeal, m.isMaximal.isPrime, Ring.liesOver_maximalIdeal_of_finite m⟩
  refine Finite.of_injective g fun m m' h => ?_
  ext1
  exact congrArg Subtype.val h

theorem Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord
    {A B K L : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Module.Finite A B] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (y : B) (hy : y ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L y)) =
      WithZero.exp (∑ᶠ m : MaximalSpectrum B,
        (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) m.asIdeal : ℤ) *
          ((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ y)).toNat : ℤ)) := by
  have hfinMS : Finite (MaximalSpectrum B) := Ring.finite_maximalSpectrum_of_finite (A := A)
  have hB : ∀ m : MaximalSpectrum B, m.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) :=
    fun m => Ring.liesOver_maximalIdeal_of_finite m
  have hfin : ∀ m : MaximalSpectrum B,
      Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) m.asIdeal ≠ 0 := fun m => by
    have := hB m
    have := m.isMaximal
    exact (Ideal.inertiaDeg'_pos (IsLocalRing.maximalIdeal A) m.asIdeal).ne'
  -- `length_A(B/yB)` is finite, so `B/yB` has finite length as a `B`-module
  have hLtop : Module.length A (B ⧸ Ideal.span {y}) ≠ ⊤ :=
    Ring.length_quotient_span_singleton_ne_top A hy
  have hflA : IsFiniteLength A (B ⧸ Ideal.span {y}) := Module.length_ne_top_iff.mp hLtop
  have hflB : IsFiniteLength B (B ⧸ Ideal.span {y}) := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hflA ⊢
    exact ⟨isNoetherian_of_tower A hflA.1, isArtinian_of_tower A hflA.2⟩
  -- 02M0 + quotients of localizations
  have h0 := Module.length_eq_inertiaLengthSum (A := A) hB hfin hflB
  unfold Module.inertiaLengthSum at h0
  simp only [Module.length_localizedModule_quotient_span_singleton] at h0
  -- 02MI
  rw [Ring.ordFrac_norm_eq_exp_length (K := K) (L := L) hy]
  congr 1
  have := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype] at h0 ⊢
  have hne : ∀ m : MaximalSpectrum B,
      Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ y) ≠ ⊤ := by
    intro m htop
    apply hLtop
    rw [h0, eq_top_iff]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ m))
    rw [htop, ENat.mul_top (by exact_mod_cast hfin m)]
  have hcoe : ∀ m : MaximalSpectrum B,
      Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ y) =
        (((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ y)).toNat : ℕ) : ℕ∞) :=
    fun m => (ENat.natCast_toNat (hne m)).symm
  rw [h0, Finset.sum_congr rfl fun m _ => by rw [hcoe m]]
  simp only [← Nat.cast_mul, ← Nat.cast_sum, ENat.toNat_natCast]

/-- From "both sides are multiplicative on `L^*`" and "they agree on `B ∖ 0`", deduce agreement on `L^*` (`B` a
domain, `L = Frac B`). This is the step extending Stacks 02MJ from `y ∈ B ∖ 0` to `y ∈ L^*`, stated separately
because the user 02RT has to perform the same step on the geometric side: there `F` is the weighted sum of
orders on the fibre and `G` is `ord(Nm(−))`, both multiplicative only on `L^*`. -/
theorem Ring.eq_of_mul_of_eq_on_algebraMap {B L : Type*} [CommRing B] [IsDomain B] [Field L]
    [Algebra B L] [IsFractionRing B L] {F G : L → ℤ}
    (hF : ∀ φ ψ : L, φ ≠ 0 → ψ ≠ 0 → F (φ * ψ) = F φ + F ψ)
    (hG : ∀ φ ψ : L, φ ≠ 0 → ψ ≠ 0 → G (φ * ψ) = G φ + G ψ)
    (hB : ∀ b : B, b ≠ 0 → F (algebraMap B L b) = G (algebraMap B L b))
    {y : L} (hy : y ≠ 0) : F y = G y := by
  obtain ⟨b, b', hb', hyb⟩ := IsFractionRing.div_surjective (A := B) y
  have hb'0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  have hb'L : algebraMap B L b' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb'0
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hyb
    exact hy hyb.symm
  have hmul : y * algebraMap B L b' = algebraMap B L b := by
    rw [← hyb, div_mul_cancel₀ _ hb'L]
  have e1 := hF y _ hy hb'L
  have e2 := hG y _ hy hb'L
  rw [hmul] at e1 e2
  rw [hB b hb0, hB b' hb'0] at e1
  linarith

/-- The general form of Stacks 02MJ (`y ∈ L^*`, the form of the original). Writing `y = b/b'`
(`IsFractionRing.div_surjective` guarantees that every `y ∈ L^*` can be so written),
`ord_A(Nm_{L/K} y) = Σ_m [κ(m):κ(m_A)]·(ord_{B_m}(b) − ord_{B_m}(b'))`.
Proof: `ordFrac` and `Algebra.norm` are multiplicative (`map_div₀`); apply the `B ∖ 0` version twice. -/
theorem Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord_of_eq_div
    {A B K L : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [Module.Finite A B] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (y : L) (b b' : B) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hy : y = algebraMap B L b / algebraMap B L b') :
    Ring.ordFrac A (Algebra.norm K y) =
      WithZero.exp (∑ᶠ m : MaximalSpectrum B,
        (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) m.asIdeal : ℤ) *
          (((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)).toNat : ℤ) -
            ((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b')).toNat : ℤ))) := by
  classical
  have hfinMS : Finite (MaximalSpectrum B) := Ring.finite_maximalSpectrum_of_finite (A := A)
  have := Fintype.ofFinite (MaximalSpectrum B)
  have hb'L : algebraMap B L b' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb'
  have hinv : Algebra.norm K ((algebraMap B L b')⁻¹) =
      (Algebra.norm K (algebraMap B L b'))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel₀ hb'L, map_one]
  have hnorm : Algebra.norm K y =
      Algebra.norm K (algebraMap B L b) / Algebra.norm K (algebraMap B L b') := by
    rw [hy, div_eq_mul_inv, map_mul, hinv, ← div_eq_mul_inv]
  rw [hnorm, map_div₀, Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord (K := K) b hb,
    Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord (K := K) b' hb', ← WithZero.exp_sub]
  congr 1
  simp only [finsum_eq_sum_of_fintype, ← Finset.sum_sub_distrib, mul_sub]

end
