import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.RingTheory.GradedRing.ReesAwayAffineBlowup

/-! # The two-generator presentation of the affine blowup algebra

Pure commutative algebra for Stacks 0AGR (steps 3–4 of the proof of
`AlgebraicGeometry.blowup_regularLocalRing_dimTwo_isRegularLocalRing_stalk`):
for an ideal `J = (a, b)` of a commutative ring `A` such that `a` is a nonzerodivisor of `A` and
`b` is a nonzerodivisor of `A/(a)`, the affine blowup algebra `A[J/a] ⊆ A_a`
(`Ideal.affineBlowup J a`) has the presentation `A[T]/(aT − b)` (`T ↦ b/a`), and consequently
`A[J/a] / (a) ≅ (A/J)[T]`.

Source: Stacks 0AGQ / 0AGR, Hartshorne V.3.1; used in the proof of Corollary 4.3 of the paper (§4). No regularity is used here; the regular local ring of
dimension two enters only through the hypotheses `a ∈ A⁰`, `b ∈ (A/a)⁰` (Stacks 00NQ).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open Polynomial

noncomputable section

namespace Ideal

variable {A : Type u} [CommRing A]

/-! ### The presentation ideal `(aT − b)` and two elementary facts about it -/

/-- `C a` is a nonzerodivisor of `A[T]` when `a` is a nonzerodivisor of `A`. -/
theorem _root_.Polynomial.C_mem_nonZeroDivisors_of_mem {a : A} (ha : a ∈ nonZeroDivisors A) :
    (C a : A[X]) ∈ nonZeroDivisors A[X] := by
  refine Polynomial.mem_nonZeroDivisors_iff.mpr fun r hr => ?_
  rw [Polynomial.smul_C, smul_eq_mul, ← Polynomial.C_0, Polynomial.C_inj] at hr
  exact (mem_nonZeroDivisors_iff_right.mp ha) r hr

/-- `aⁿ · p ≡ c (mod (aT − b))` for a constant `c ∈ A` whenever `deg p < n`
(replace `aT` by `b` in `aⁿ p = ∑ pᵢ aⁿ⁻ⁱ (aT)ⁱ`). -/
theorem exists_C_pow_mul_sub_C_mem_span (a b : A) (p : A[X]) (n : ℕ) (hn : p.natDegree < n) :
    ∃ c : A, (C a) ^ n * p - C c ∈ Ideal.span {C a * X - C b} := by
  refine ⟨∑ i ∈ Finset.range n, p.coeff i * a ^ (n - i) * b ^ i, ?_⟩
  nth_rw 1 [p.as_sum_range' n hn]
  rw [Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ n := (Finset.mem_range.mp hi).le
  have hpow : (C a : A[X]) ^ n = C a ^ (n - i) * C a ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [← Polynomial.C_mul_X_pow_eq_monomial, hpow, map_mul, map_mul, map_pow, map_pow]
  have : C a ^ (n - i) * C a ^ i * (C (p.coeff i) * X ^ i) - C (p.coeff i) * C a ^ (n - i) * C b ^ i =
      (C (p.coeff i) * C a ^ (n - i)) * ((C a * X) ^ i - (C b) ^ i) := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.mpr (sub_dvd_pow_sub_pow _ _ i))

/-- `a` is a nonzerodivisor of `A[T]/(aT − b)`: if `a·q ∈ (aT − b)` then `q ∈ (aT − b)`.
Write `a q = (aT − b) h`; reducing modulo `a` gives `−b̄ h̄ = 0` in `(A/a)[T]`, so `h̄ = 0` because
`b̄` is a nonzerodivisor of `A/a`; hence `h = a h'`, and cancelling `a` (a nonzerodivisor of `A[T]`)
gives `q = (aT − b) h'`. -/
theorem mem_span_of_C_mul_mem_span {a b : A} (ha : a ∈ nonZeroDivisors A)
    (hb : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a}) (q : A[X])
    (hq : C a * q ∈ Ideal.span {C a * X - C b}) : q ∈ Ideal.span {C a * X - C b} := by
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton.mp hq
  -- reduce modulo `a`
  set π : A[X] →+* (A ⧸ Ideal.span {a})[X] := Polynomial.mapRingHom (Ideal.Quotient.mk _)
  have hπa : π (C a) = 0 := by
    simp [π, Polynomial.coe_mapRingHom, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self a)]
  have hmod : C (Ideal.Quotient.mk (Ideal.span {a}) b) * π h = 0 := by
    have := congrArg π hh
    rw [map_mul, hπa, zero_mul, map_mul, map_sub, map_mul, hπa, zero_mul, zero_sub, neg_mul] at this
    have := neg_eq_zero.mp this.symm
    simpa [π, Polynomial.coe_mapRingHom] using this
  have hbnzd : (C (Ideal.Quotient.mk (Ideal.span {a}) b) : (A ⧸ Ideal.span {a})[X]) ∈
      nonZeroDivisors (A ⧸ Ideal.span {a})[X] := by
    refine Polynomial.C_mem_nonZeroDivisors_of_mem (mem_nonZeroDivisors_iff_right.mpr fun r hr => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hb x (by rwa [mul_comm]))
  have hπh : π h = 0 := (mem_nonZeroDivisors_iff_right.mp hbnzd) _ (by rwa [mul_comm])
  -- so every coefficient of `h` is divisible by `a`
  have hdvd : C a ∣ h := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have : h ∈ RingHom.ker π := hπh
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.mem_map_C_iff] at this
    exact Ideal.mem_span_singleton.mp (this i)
  obtain ⟨h', rfl⟩ := hdvd
  refine Ideal.mem_span_singleton.mpr ⟨h', ?_⟩
  have hC := Polynomial.C_mem_nonZeroDivisors_of_mem ha
  refine (mul_cancel_left_mem_nonZeroDivisors hC).mp ?_
  rw [hh]; ring

/-! ### The presentation `A[T] → A[J/a]`, `T ↦ b/a` -/

variable (J : Ideal A) (a : A)

/-- `b/a ∈ A[J/a]` as an element of the affine blowup algebra, for `b ∈ J`. -/
def affineBlowupFraction (b : A) (hb : b ∈ J) : J.affineBlowup a :=
  ⟨IsLocalization.mk' (Localization.Away a) b ⟨a, Submonoid.mem_powers a⟩,
    J.mk'_mem_affineBlowup_of_mem a b hb⟩

theorem coe_affineBlowupFraction (b : A) (hb : b ∈ J) :
    ((J.affineBlowupFraction a b hb : J.affineBlowup a) : Localization.Away a) =
      IsLocalization.mk' (Localization.Away a) b ⟨a, Submonoid.mem_powers a⟩ := rfl

/-- `a · (b/a) = b` in `A[J/a]`. -/
theorem algebraMap_mul_affineBlowupFraction (b : A) (hb : b ∈ J) :
    algebraMap A (J.affineBlowup a) a * J.affineBlowupFraction a b hb =
      algebraMap A (J.affineBlowup a) b := by
  apply Subtype.ext
  change algebraMap A (Localization.Away a) a *
      IsLocalization.mk' (Localization.Away a) b ⟨a, Submonoid.mem_powers a⟩ =
    algebraMap A (Localization.Away a) b
  rw [mul_comm]
  exact IsLocalization.mk'_spec (Localization.Away a) b ⟨a, Submonoid.mem_powers a⟩

/-- The presentation `A[T] → A[J/a]`, `T ↦ b/a`. -/
def affineBlowupPresentation (b : A) (hb : b ∈ J) : A[X] →ₐ[A] J.affineBlowup a :=
  Polynomial.aeval (J.affineBlowupFraction a b hb)

theorem affineBlowupPresentation_X (b : A) (hb : b ∈ J) :
    J.affineBlowupPresentation a b hb X = J.affineBlowupFraction a b hb :=
  Polynomial.aeval_X _

theorem affineBlowupPresentation_C (b : A) (hb : b ∈ J) (r : A) :
    J.affineBlowupPresentation a b hb (C r) = algebraMap A (J.affineBlowup a) r :=
  Polynomial.aeval_C _ _

/-- `aT − b` lies in the kernel of the presentation. -/
theorem span_le_ker_affineBlowupPresentation (b : A) (hb : b ∈ J) :
    Ideal.span {C a * X - C b} ≤ RingHom.ker (J.affineBlowupPresentation a b hb).toRingHom := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
  change J.affineBlowupPresentation a b hb (C a * X - C b) = 0
  rw [map_sub, map_mul, affineBlowupPresentation_X, affineBlowupPresentation_C,
    affineBlowupPresentation_C, algebraMap_mul_affineBlowupFraction, sub_self]

/-- Surjectivity of the presentation when `J = (a, b)`: `A[J/a]` is generated by the fractions
`m/a`, `m ∈ J`, and `m = α a + β b` gives `m/a = α + β·(b/a)`. -/
theorem affineBlowupPresentation_surjective (b : A) (hb : b ∈ J) (hJ : J = Ideal.span {a, b}) :
    Function.Surjective (J.affineBlowupPresentation a b hb) := by
  intro z
  set φ := J.affineBlowupPresentation a b hb
  -- the range of `A[T] → A[J/a] ⊆ A_a` contains the generators `m/a` of `A[J/a]`
  have hgen : J.affineBlowup a ≤ ((J.affineBlowup a).val.comp φ).range := by
    change Algebra.adjoin A _ ≤ _
    refine Algebra.adjoin_le ?_
    rintro _ ⟨m, hm, rfl⟩
    rw [hJ] at hm
    obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hm
    refine ⟨C α + C β * X, ?_⟩
    show ((J.affineBlowup a).val.comp φ) (C α + C β * X) = _
    rw [AlgHom.comp_apply, map_add, map_mul, affineBlowupPresentation_C, affineBlowupPresentation_C,
      affineBlowupPresentation_X]
    simp only [Subalgebra.coe_val, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap, coe_affineBlowupFraction]
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    unfold IsLocalization.Away.invSelf
    have h1 : algebraMap A (Localization.Away a) a *
        IsLocalization.mk' (Localization.Away a) (1 : A) ⟨a, Submonoid.mem_powers a⟩ = 1 := by
      have := IsLocalization.mk'_spec' (Localization.Away a) (1 : A) ⟨a, Submonoid.mem_powers a⟩
      rwa [map_one] at this
    rw [map_add, map_mul, map_mul]
    linear_combination (-(algebraMap A (Localization.Away a) α)) * h1
  obtain ⟨p, hp⟩ := hgen z.2
  exact ⟨p, Subtype.ext hp⟩

/-- The kernel of the presentation is contained in `(aT − b)` when `a ∈ A⁰` and `b ∈ (A/a)⁰`:
if `p(b/a) = 0` in `A_a`, then `aⁿ p ≡ c (mod (aT − b))` with `c ∈ A` (`exists_C_pow_mul_sub_C_mem_span`),
`c/1 = aⁿ p(b/a) = 0` forces `c = 0` (`a` a nonzerodivisor), so `aⁿ p ∈ (aT − b)`, and `a` is a
nonzerodivisor modulo `(aT − b)` (`mem_span_of_C_mul_mem_span`). -/
theorem ker_affineBlowupPresentation_le (b : A) (hb : b ∈ J) (ha : a ∈ nonZeroDivisors A)
    (hb' : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a}) :
    RingHom.ker (J.affineBlowupPresentation a b hb).toRingHom ≤ Ideal.span {C a * X - C b} := by
  intro p hp
  rw [RingHom.mem_ker] at hp
  change J.affineBlowupPresentation a b hb p = 0 at hp
  obtain ⟨c, hc⟩ := exists_C_pow_mul_sub_C_mem_span a b p (p.natDegree + 1) (Nat.lt_succ_self _)
  have hker := J.span_le_ker_affineBlowupPresentation a b hb hc
  rw [RingHom.mem_ker] at hker
  change J.affineBlowupPresentation a b hb (C a ^ (p.natDegree + 1) * p - C c) = 0 at hker
  rw [map_sub, map_mul, hp, mul_zero, zero_sub, neg_eq_zero, affineBlowupPresentation_C] at hker
  have hc0 : c = 0 := by
    have h1 : algebraMap A (Localization.Away a) c = 0 := congrArg Subtype.val hker
    exact (IsLocalization.to_map_eq_zero_iff (Localization.Away a) (M := Submonoid.powers a)
      (Submonoid.powers_le.mpr ha)).mp h1
  rw [hc0, map_zero, sub_zero] at hc
  have key : ∀ n : ℕ, ∀ q : A[X], C a ^ n * q ∈ Ideal.span {C a * X - C b} →
      q ∈ Ideal.span {C a * X - C b} := by
    intro n
    induction n with
    | zero => intro q hq; simpa using hq
    | succ n ih =>
      intro q hq
      rw [pow_succ, mul_assoc] at hq
      exact mem_span_of_C_mul_mem_span ha hb' q (ih _ hq)
  exact key _ p hc

theorem ker_affineBlowupPresentation_eq (b : A) (hb : b ∈ J) (ha : a ∈ nonZeroDivisors A)
    (hb' : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a}) :
    RingHom.ker (J.affineBlowupPresentation a b hb).toRingHom = Ideal.span {C a * X - C b} :=
  le_antisymm (J.ker_affineBlowupPresentation_le a b hb ha hb')
    (J.span_le_ker_affineBlowupPresentation a b hb)

/-- **`A[J/a] ≅ A[T]/(aT − b)`** for `J = (a, b)`, `a ∈ A⁰`, `b ∈ (A/a)⁰` (Stacks 0AGR, step 3). -/
def affineBlowupPresentationEquiv (b : A) (hb : b ∈ J) (hJ : J = Ideal.span {a, b})
    (ha : a ∈ nonZeroDivisors A) (hb' : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a}) :
    (A[X] ⧸ Ideal.span {C a * X - C b}) ≃+* J.affineBlowup a :=
  (Ideal.quotEquivOfEq (J.ker_affineBlowupPresentation_eq a b hb ha hb').symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (J.affineBlowupPresentation a b hb).toRingHom)
      (J.affineBlowupPresentation_surjective a b hb hJ))

theorem affineBlowupPresentationEquiv_mk (b : A) (hb : b ∈ J) (hJ : J = Ideal.span {a, b})
    (ha : a ∈ nonZeroDivisors A) (hb' : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a})
    (p : A[X]) :
    J.affineBlowupPresentationEquiv a b hb hJ ha hb' (Ideal.Quotient.mk _ p) =
      J.affineBlowupPresentation a b hb p := rfl

/-- **`A[J/a]/(a) ≅ (A/J)[T]`** for `J = (a, b)`, `a ∈ A⁰`, `b ∈ (A/a)⁰` (Stacks 0AGR, step 4):
`A[J/a]/(a) ≅ A[T]/(aT − b, a) = A[T]/(a, b) = A[T]/J·A[T] ≅ (A/J)[T]`. -/
theorem affineBlowup_quotient_span_algebraMap_equiv_polynomial (b : A) (hb : b ∈ J)
    (hJ : J = Ideal.span {a, b}) (ha : a ∈ nonZeroDivisors A)
    (hb' : ∀ x : A, b * x ∈ Ideal.span {a} → x ∈ Ideal.span {a}) :
    Nonempty ((J.affineBlowup a ⧸ Ideal.span {algebraMap A (J.affineBlowup a) a}) ≃+* (A ⧸ J)[X]) := by
  obtain ⟨e, he⟩ : ∃ e : (A[X] ⧸ Ideal.span {C a * X - C b}) ≃+* J.affineBlowup a,
      ∀ p : A[X], e (Ideal.Quotient.mk _ p) = J.affineBlowupPresentation a b hb p :=
    ⟨_, J.affineBlowupPresentationEquiv_mk a b hb hJ ha hb'⟩
  have hmap : Ideal.span {algebraMap A (J.affineBlowup a) a} =
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {C a * X - C b}) (C a)}).map
        (e : A[X] ⧸ Ideal.span {C a * X - C b} →+* J.affineBlowup a) := by
    rw [Ideal.map_span, Set.image_singleton]
    change _ = Ideal.span {e (Ideal.Quotient.mk _ (C a))}
    rw [he, affineBlowupPresentation_C]
  let e1 : (A[X] ⧸ Ideal.span {C a * X - C b}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {C a * X - C b}) (C a)} ≃+*
      J.affineBlowup a ⧸ Ideal.span {algebraMap A (J.affineBlowup a) a} :=
    Ideal.quotientEquiv _ _ e hmap
  have hspan : Ideal.span {Ideal.Quotient.mk (Ideal.span {C a * X - C b}) (C a)} =
      (Ideal.span {C a}).map (Ideal.Quotient.mk (Ideal.span {C a * X - C b})) := by
    rw [Ideal.map_span, Set.image_singleton]
  let e2 : (A[X] ⧸ Ideal.span {C a * X - C b}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {C a * X - C b}) (C a)} ≃+*
      A[X] ⧸ (Ideal.span {C a * X - C b} ⊔ Ideal.span {C a}) :=
    (Ideal.quotEquivOfEq hspan).trans
      (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {C a * X - C b}) (Ideal.span {C a}))
  have hsup : Ideal.span {C a * X - C b} ⊔ Ideal.span {C a} = J.map (C : A →+* A[X]) := by
    rw [hJ, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, Ideal.span_insert]
    apply le_antisymm
    · refine sup_le ?_ le_sup_left
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      exact Ideal.sub_mem _
        (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (C a))))
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (C b)))
    · refine sup_le le_sup_right ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have h1 : (C a * X : A[X]) ∈ Ideal.span {C a * X - C b} ⊔ Ideal.span {C a} :=
        Ideal.mem_sup_right (Ideal.mul_mem_right X _ (Ideal.mem_span_singleton_self (C a)))
      have h2 : (C a * X - C b : A[X]) ∈ Ideal.span {C a * X - C b} ⊔ Ideal.span {C a} :=
        Ideal.mem_sup_left (Ideal.mem_span_singleton_self (C a * X - C b))
      have h3 := Ideal.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at h3
  exact ⟨e1.symm.trans (e2.trans ((Ideal.quotEquivOfEq hsup).trans
    (Ideal.polynomialQuotientEquivQuotientPolynomial J).symm))⟩

end Ideal

end
