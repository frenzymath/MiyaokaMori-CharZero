import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agrChartPresentation
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nq
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nqRegularSequence
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nu

/-! # Regularity of the exceptional fibre of the blowup of a two-dimensional regular local ring

Stacks 0AGR, the commutative-algebra core:
for a regular local ring `(A, 𝔪, κ)` of dimension `2`, `a ∈ 𝔪`, and a prime `𝔮` of the affine blowup
algebra `A[𝔪/a] ⊆ A_a` (`Ideal.affineBlowup 𝔪 a`) lying over `𝔪` (`𝔮 ∩ A = 𝔪`, i.e. a point of the
exceptional fibre of the chart `Spec A[𝔪/a]` of `Bl_𝔪 Spec A`), the local ring `A[𝔪/a]_𝔮` is regular.

Source: Stacks 0AGR (Lemma "resolve-lemma-blowup-regular"), 0AGQ; Hartshorne V.3.1; the point blowups in the
ruled-surface realization of the paper. Inputs: Stacks 00NQ (a minimal generating set of `𝔪` is a regular
sequence), the presentation `A[𝔪/a]/(a) ≅ κ[T]` of the affine blowup algebra, Stacks 00NU (`R/xR` regular and
`x` a nonzerodivisor ⇒ `R` regular).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open Polynomial
open scoped Pointwise

noncomputable section

namespace Ideal

variable {A : Type u} [CommRing A]

/-- If a prime `𝔮` of `A[J/a]` lies over an ideal containing `J` (`J ≤ 𝔮 ∩ A`), then `a ∉ J²`:
`J·A[J/a] = (a)` (`MiyaokaMori.RingTheory.IdealFractionChart.centerExtension_eq_span`), so `a ∈ J²` would give
`a = a²·c` in `A[J/a]`, hence `1 = a·c` (`a` is a nonzerodivisor of `A[J/a]`), i.e. `1 ∈ J·A[J/a] ⊆ 𝔮`.
Geometrically: the chart `V_a` misses the exceptional fibre when `a ∈ J²`. -/
theorem notMem_sq_of_affineBlowup_le_comap (J : Ideal A) (a : A) (ha : a ∈ J)
    (𝔮 : Ideal (J.affineBlowup a)) [𝔮.IsPrime]
    (h𝔮 : J ≤ 𝔮.comap (algebraMap A (J.affineBlowup a))) : a ∉ J ^ 2 := by
  intro ha2
  have hspan : J.map (algebraMap A (J.affineBlowup a)) =
      Ideal.span {algebraMap A (J.affineBlowup a) a} :=
    MiyaokaMori.RingTheory.IdealFractionChart.centerExtension_eq_span J a ha
  have hnzd : ∀ r : J.affineBlowup a, algebraMap A (J.affineBlowup a) a * r = 0 → r = 0 :=
    MiyaokaMori.RingTheory.IdealFractionChart.generator_mul_eq_zero J a
  have h1 : algebraMap A (J.affineBlowup a) a ∈
      Ideal.span {algebraMap A (J.affineBlowup a) a} ^ 2 := by
    rw [← hspan, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha2
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : algebraMap A (J.affineBlowup a) a * (1 - algebraMap A (J.affineBlowup a) a * c) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, ← hc, sub_self]
  have h3 := sub_eq_zero.mp (hnzd _ h2)
  have h4 : (1 : J.affineBlowup a) ∈ 𝔮 := by
    rw [h3]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_comap.mp (h𝔮 ha))
  exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr h4)

/-- Steps 4–6 of Stacks 0AGR in abstract form: `B` Noetherian, `𝔮 ⊆ B` prime, `R` the localization
`B_𝔮`, `b ∈ 𝔮` a nonzerodivisor of `B` with `B/(b)` a regular ring. Then `R` is a regular local ring:
`x := b/1 ∈ 𝔪_R` is a nonzerodivisor of `R` (localization preserves nonzerodivisors), and
`R/xR ≅ (B/(b))_𝔮̄` (Mathlib: localization commutes with quotients; the submonoid `(B ∖ 𝔮)/(b)` is the
complement of the prime `𝔮̄ = 𝔮/(b)` since `(b) ⊆ 𝔮`) is a localization of a regular ring at a prime,
hence regular local; conclude with Stacks 00NU
(`IsRegularLocalRing.of_quotient_span_singleton_of_mem_nonZeroDivisors`).
Stated for an abstract `R` because instance search on `Localization.AtPrime 𝔮 ⧸ I` is very slow. -/
theorem isRegularLocalRing_of_isLocalization_atPrime_of_isRegularRing_quotient
    {B : Type u} [CommRing B] [IsNoetherianRing B] (𝔮 : Ideal B) [𝔮.IsPrime]
    (R : Type u) [CommRing R] [Algebra B R] [IsLocalization.AtPrime R 𝔮]
    (b : B) (hb : b ∈ 𝔮) (hb_nzd : b ∈ nonZeroDivisors B)
    [IsRegularRing (B ⧸ Ideal.span {b})] : IsRegularLocalRing R := by
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔮
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing 𝔮.primeCompl R inferInstance
  have hx : algebraMap B R b ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 R]
    exact Ideal.mem_map_of_mem _ hb
  have hx_nzd : algebraMap B R b ∈ nonZeroDivisors R :=
    IsLocalization.map_nonZeroDivisors_le 𝔮.primeCompl R (Submonoid.mem_map_of_mem _ hb_nzd)
  have hxspan : (Ideal.span {b}).map (algebraMap B R) = Ideal.span {algebraMap B R b} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hb𝔮 : Ideal.span {b} ≤ 𝔮 := (Ideal.span_singleton_le_iff_mem _).mpr hb
  have hprime : (𝔮.map (Ideal.Quotient.mk (Ideal.span {b}))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hb𝔮)
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ Ideal.span {b}) 𝔮.primeCompl =
      (𝔮.map (Ideal.Quotient.mk (Ideal.span {b}))).primeCompl := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change Ideal.Quotient.mk _ y ∉ _
      intro hz
      have h1 : y ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {b})) (𝔮.map _) :=
        Ideal.mem_comap.mpr hz
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hb𝔮] at h1
      exact hy h1
    · intro hz
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨y, fun hy => hz (Ideal.mem_map_of_mem _ hy), rfl⟩
  have : IsLocalization (𝔮.map (Ideal.Quotient.mk (Ideal.span {b}))).primeCompl
      (R ⧸ (Ideal.span {b}).map (algebraMap B R)) := by
    rw [← hsub]; infer_instance
  have : IsRegularLocalRing (R ⧸ (Ideal.span {b}).map (algebraMap B R)) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv (𝔮.map (Ideal.Quotient.mk (Ideal.span {b}))).primeCompl
        (Localization.AtPrime (𝔮.map (Ideal.Quotient.mk (Ideal.span {b}))))
        (R ⧸ (Ideal.span {b}).map (algebraMap B R))).toRingEquiv
  rw [hxspan] at this
  exact IsRegularLocalRing.of_quotient_span_singleton_of_mem_nonZeroDivisors hx hx_nzd

/-- **Stacks 0AGR, algebraic core.** `(A, 𝔪, κ)` regular local of dimension `2`, `J = 𝔪`, `a ∈ 𝔪`, and
`𝔮` a prime of `A[𝔪/a]` with `𝔮 ∩ A = 𝔪`. Then `A[𝔪/a]_𝔮` is a regular local ring.

Proof (Stacks 0AGR / 0AGQ):
1. `a ∉ 𝔪²` (`notMem_sq_of_affineBlowup_le_comap`), so `a` extends to a minimal generating set
   `𝔪 = (a, b)` (`IsLocalRing.exists_finset_span_insert_eq_maximalIdeal`, `spanFinrank 𝔪 = dim A = 2`;
   `𝔪 = (a)` is impossible since `spanFinrank 𝔪 = 2`).
2. `a, b` is a regular sequence (Stacks 00NQ,
   `IsRegularLocalRing.isWeaklyRegular_of_span_eq_maximalIdeal`): `a ∈ A⁰`, `b ∈ (A/a)⁰`.
3. `A[𝔪/a]/(a) ≅ κ[T]` (`Ideal.affineBlowup_quotient_span_algebraMap_equiv_polynomial`), a regular
   ring (`κ[T]` is a PID, hence Dedekind, hence `IsRegularRing`).
4. `R := A[𝔪/a]_𝔮` is Noetherian local (`A[𝔮/a]` is a quotient of `A[T]`), `x := a/1 ∈ 𝔪_R` (as `a ∈ 𝔮`),
   `x ∈ R⁰` (`a ∈ A[𝔪/a]⁰`, localization), and `R/xR ≅ (A[𝔪/a]/(a))_𝔮̄` (Mathlib: localization of a
   quotient) is a localization of a regular ring at a prime, hence regular local.
5. Stacks 00NU (`IsRegularLocalRing.of_quotient_span_singleton_of_mem_nonZeroDivisors`): `R` is regular. -/
theorem affineBlowup_isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (J : Ideal A) (hJ : J = IsLocalRing.maximalIdeal A) (a : A) (ha : a ∈ J)
    (𝔮 : Ideal (J.affineBlowup a)) [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (algebraMap A (J.affineBlowup a)) = IsLocalRing.maximalIdeal A) :
    IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  subst hJ
  -- Step 1: `𝔪 = (a, b)`.
  have ha2 : a ∉ IsLocalRing.maximalIdeal A ^ 2 :=
    Ideal.notMem_sq_of_affineBlowup_le_comap _ a ha 𝔮 h𝔮.ge
  have hrank : (IsLocalRing.maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨s, hs, hspan⟩ := IsLocalRing.exists_finset_span_insert_eq_maximalIdeal ha ha2
  rw [hrank] at hs
  obtain ⟨b, rfl⟩ : ∃ b, s = {b} := by
    rcases Nat.lt_or_ge s.card 1 with h | h
    · exfalso
      rw [Nat.lt_one_iff, Finset.card_eq_zero] at h
      subst h
      have h1 := Submodule.spanFinrank_span_le_ncard_of_finite
        (R := A) (M := A) (s := insert a ((∅ : Finset A) : Set A)) (by simp)
      rw [show Submodule.span A (insert a ((∅ : Finset A) : Set A)) = IsLocalRing.maximalIdeal A from
        hspan, hrank] at h1
      simp at h1
    · exact Finset.card_eq_one.mp (le_antisymm (by omega) h)
  rw [Finset.coe_singleton] at hspan
  have hb : b ∈ IsLocalRing.maximalIdeal A := hspan ▸ Ideal.subset_span (by simp)
  -- Step 2: `a, b` is a regular sequence.
  have hreg : RingTheory.Sequence.IsWeaklyRegular A [a, b] := by
    have hrange : Set.range ![a, b] = {a, b} := by
      ext x
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
    have := IsRegularLocalRing.isWeaklyRegular_of_span_eq_maximalIdeal hdim ![a, b]
      (by rw [hrange]; exact hspan)
    simpa [List.ofFn_succ] using this
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hreg
  obtain ⟨hreg_a, hreg_b⟩ := hreg
  have ha_nzd : a ∈ nonZeroDivisors A := by
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
    exact hreg_a (show a • x = a • 0 by rw [smul_zero, smul_eq_mul, mul_comm]; exact hx)
  have hsmul : (a • (⊤ : Submodule A A)) = (Ideal.span {a} : Ideal A) := by
    rw [← Submodule.ideal_span_singleton_smul]; simp
  have hb_nzd : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a} := by
    intro x hx
    have h1 : b • (Submodule.Quotient.mk x : QuotSMulTop a A) = b • 0 := by
      rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsmul]
      exact hx
    have h2 := hreg_b h1
    rw [Submodule.Quotient.mk_eq_zero, hsmul] at h2
    exact h2
  -- Step 3: `A[𝔪/a]/(a) ≅ κ[T]` is a regular ring.
  obtain ⟨e⟩ := (IsLocalRing.maximalIdeal A).affineBlowup_quotient_span_algebraMap_equiv_polynomial
    a b hb hspan.symm ha_nzd hb_nzd
  have : IsRegularRing (A ⧸ IsLocalRing.maximalIdeal A)[X] :=
    inferInstanceAs (IsRegularRing (IsLocalRing.ResidueField A)[X])
  have : IsRegularRing ((IsLocalRing.maximalIdeal A).affineBlowup a ⧸
      Ideal.span {algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a) a}) :=
    IsRegularRing.of_ringEquiv e.symm
  -- Step 4: the local ring `R = A[𝔪/a]_𝔮` and the element `x = a/1`.
  have : IsNoetherianRing ((IsLocalRing.maximalIdeal A).affineBlowup a) :=
    isNoetherianRing_of_surjective A[X] _
      ((IsLocalRing.maximalIdeal A).affineBlowupPresentation a b hb).toRingHom
      ((IsLocalRing.maximalIdeal A).affineBlowupPresentation_surjective a b hb hspan.symm)
  have hā𝔮 : algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a) a ∈ 𝔮 :=
    Ideal.mem_comap.mp (by rw [h𝔮]; exact ha)
  have hnzd : ∀ r : (IsLocalRing.maximalIdeal A).affineBlowup a,
      algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a) a * r = 0 → r = 0 :=
    MiyaokaMori.RingTheory.IdealFractionChart.generator_mul_eq_zero (IsLocalRing.maximalIdeal A) a
  have hā_nzd : algebraMap A ((IsLocalRing.maximalIdeal A).affineBlowup a) a ∈
      nonZeroDivisors ((IsLocalRing.maximalIdeal A).affineBlowup a) :=
    mem_nonZeroDivisors_iff_right.mpr fun r hr => hnzd r (by rw [mul_comm]; exact hr)
  -- Steps 4–5: localize and apply Stacks 00NU.
  exact Ideal.isRegularLocalRing_of_isLocalization_atPrime_of_isRegularRing_quotient 𝔮
    (Localization.AtPrime 𝔮) _ hā𝔮 hā_nzd

end Ideal

end
