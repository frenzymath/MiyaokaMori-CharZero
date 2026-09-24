import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Length.PeriodicComplexLength
import MiyaokaMori.RingTheory.Length.PeriodicComplexMultiply

/-! # Definitions for the Key Lemma (Stacks 0EAW)

The definitions used in the semi-local version of Stacks 0EAW (the Key Lemma in the nonzerodivisor
case): the symbolic powers `KeyLemma.symbPow` of a prime `𝔭` of a finite `A`-algebra `B`, the
`A`-linear endomorphism `KeyLemma.mulQ` "multiplication by `x`" on `B/I`,
`KeyLemma.lam A 𝔭 y = length_A(B/(𝔭 + yB))`, the contraction `KeyLemma.contr` of a principal ideal at
`𝔭`, and the multiplicity `KeyLemma.Hsym` of the `(2,1)`-periodic complex at each prime (the
`e_A(M_i, a, b)` in the proof of Stacks 0EAW).

References: the notation `M_i`, `e_A(M_i, a, b)` in the second paragraph of the proof of Stacks 0EAW
(chow-lemma-key-nonzerodivisors); Stacks 02PH (definition of `e_R`).
-/

set_option autoImplicit false

universe u

noncomputable section

namespace KeyLemma

variable (A : Type u) {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The `n`-th symbolic power `𝔭^(n) = 𝔭ⁿB_𝔭 ∩ B` of `𝔭` (when `B_𝔭` is a DVR, this is `{x | ord_𝔭 x ≥ n}`). -/
def symbPow (𝔭 : Ideal B) [𝔭.IsPrime] (n : ℕ) : Ideal B :=
  Ideal.comap (algebraMap B (Localization.AtPrime 𝔭))
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ^ n)

/-- The contraction `tB_𝔭 ∩ B` of the principal ideal `tB` at the prime `𝔭`. The `M_i` of Stacks 0EAW is
`B ⧸ contr 𝔭 (ab)`. -/
def contr (𝔭 : PrimeSpectrum B) (t : B) : Ideal B :=
  Ideal.comap (algebraMap B (Localization.AtPrime 𝔭.asIdeal))
    (Ideal.span {algebraMap B (Localization.AtPrime 𝔭.asIdeal) t})

/-- Multiplication by `x` on `B ⧸ I`, as an `A`-linear endomorphism. -/
def mulQ (I : Ideal B) (x : B) : (B ⧸ I) →ₗ[A] (B ⧸ I) :=
  (LinearMap.mulLeft B (Ideal.Quotient.mk I x)).restrictScalars A

/-- `λ_𝔭(y) = length_A(B/(𝔭 + yB))` (as a natural number when finite; `0` when `⊤`, and all uses carry a
finiteness hypothesis). By Stacks 02MI it equals `ord_{A/q}(Nm_{κ(𝔭)/κ(q)}(ȳ))` with `q = 𝔭 ∩ A`. -/
def lam (𝔭 : Ideal B) (y : B) : ℕ :=
  (Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y}))).toNat

/-- The `e_A(M_𝔭, a, b)` of Stacks 0EAW, with `M_𝔭 = B ⧸ (abB_𝔭 ∩ B)`. -/
def Hsym (a b : B) (𝔭 : PrimeSpectrum B) : ℤ :=
  PeriodicComplex.herbrand (mulQ A (contr 𝔭 (a * b)) a) (mulQ A (contr 𝔭 (a * b)) b)

variable {A}

@[simp] theorem mulQ_apply (I : Ideal B) (x : B) (m : B ⧸ I) :
    mulQ A I x m = Ideal.Quotient.mk I x * m := rfl

theorem mulQ_mul (I : Ideal B) (x y : B) : mulQ A I (x * y) = mulQ A I x ∘ₗ mulQ A I y := by
  refine LinearMap.ext fun m => ?_
  simp only [mulQ_apply, LinearMap.comp_apply, map_mul, mul_assoc]

theorem mulQ_comm (I : Ideal B) (x y : B) : mulQ A I x ∘ₗ mulQ A I y = mulQ A I y ∘ₗ mulQ A I x := by
  rw [← mulQ_mul, ← mulQ_mul, mul_comm]

theorem mulQ_pow (I : Ideal B) (x : B) (n : ℕ) : mulQ A I (x ^ n) = (mulQ A I x) ^ n := by
  induction n with
  | zero =>
    refine LinearMap.ext fun m => ?_
    simp only [mulQ_apply, pow_zero, map_one, one_mul, Module.End.one_apply]
  | succ n ih => rw [pow_succ, mulQ_mul, ih, pow_succ, Module.End.mul_eq_comp]

/-- Multiplication by `y` preserves the image of multiplication by `x` (the hypothesis `χ(Im φ) ⊂ Im φ`
of 0EAC). -/
theorem range_mulQ_le_comap (I : Ideal B) (x y : B) :
    LinearMap.range (mulQ A I x) ≤ (LinearMap.range (mulQ A I x)).comap (mulQ A I y) := by
  rintro _ ⟨m, rfl⟩
  exact ⟨mulQ A I y m, by simp only [mulQ_apply, mul_left_comm]⟩

/-- Elements with product in `I` give a complex: `xy ∈ I ⇒ (mult. by x) ∘ (mult. by y) = 0`. -/
theorem mulQ_comp_eq_zero (I : Ideal B) {x y : B} (h : x * y ∈ I) :
    mulQ A I x ∘ₗ mulQ A I y = 0 := by
  refine LinearMap.ext fun m => ?_
  have h0 : Ideal.Quotient.mk I x * Ideal.Quotient.mk I y = 0 := by
    rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  simp only [LinearMap.comp_apply, mulQ_apply, ← mul_assoc, h0, zero_mul, LinearMap.zero_apply]

end KeyLemma

end
