import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs

/-! # Additivity of `λ_𝔭`

`λ_𝔭(y) = length_A(B/(𝔭+yB))` is additive on `B ∖ 𝔭`: `λ(yy′) = λ(y) + λ(y′)` (`B/𝔭` is a domain,
`0 → D/y′ → D/yy′ → D/y → 0`); consequently `λ(1) = 0`, `λ(−y) = λ(y)`, `λ(y^n) = nλ(y)`.

Reference: Stacks 02MD/00PF (additivity of `ord`; the `A`-length version of `Ring.ord_mul`).
-/

set_option autoImplicit false

universe u

open PeriodicComplex Pointwise

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (𝔭 : Ideal B) [𝔭.IsPrime]

omit [𝔭.IsPrime] in
/-- `(B/𝔭)/(z̄) ≅ B/(𝔭 + zB)` as `A`-modules (`DoubleQuot.quotQuotEquivQuotSupₐ`), so the lengths agree.
(The same fact as `TameOrdBridge.length_quotient_quotient_span_eq`; reproved locally so that this file
does not depend on a downstream module.) -/
theorem length_quot_sup_span_eq_quot_quot (z : B) :
    Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {z})) =
      Module.length A ((B ⧸ 𝔭) ⧸ Ideal.span {Ideal.Quotient.mk 𝔭 z}) := by
  have h : Ideal.span {Ideal.Quotient.mk 𝔭 z} = (Ideal.span {z}).map (Ideal.Quotient.mkₐ A 𝔭) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  rw [h]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A 𝔭 (Ideal.span {z})).toLinearEquiv.length_eq.symm

/-- The `ℕ∞`-valued version: `length_A(B/(𝔭 + yy′B)) = length_A(B/(𝔭 + yB)) + length_A(B/(𝔭 + y′B))` for
`y′ ∉ 𝔭`.
Proof: let `D = B ⧸ 𝔭` (a domain) and pass to `D/(ȳ)`; `ȳ′` is a nonzerodivisor of `D`, and Mathlib's
short exact sequence of `D`-modules `0 → D/(ȳ) --·ȳ′--> D/(ȳ′·(ȳ)) → D/(ȳ′) → 0`
(`Ideal.mulQuot`/`Ideal.quotOfMul`, as in the proof of `Ring.ord_mul`) stays exact after restricting
scalars to `A` (same underlying maps), so `Module.length_eq_add_of_exact` applies; finally
`ȳ′·(ȳ) = (ȳȳ′)`. -/
theorem length_quot_sup_span_mul {y' : B} (hy' : y' ∉ 𝔭) (y : B) :
    Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y * y'})) =
      Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) + Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y'})) := by
  rw [length_quot_sup_span_eq_quot_quot, length_quot_sup_span_eq_quot_quot,
    length_quot_sup_span_eq_quot_quot]
  set D := B ⧸ 𝔭
  set a : D := Ideal.Quotient.mk 𝔭 y
  set b : D := Ideal.Quotient.mk 𝔭 y'
  have hb : b ∈ nonZeroDivisors D :=
    mem_nonZeroDivisors_of_ne_zero fun h => hy' (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hab : (Ideal.Quotient.mk 𝔭 (y * y') : D) = b * a := by
    simp only [a, b, map_mul, mul_comm]
  have hI : b • Ideal.span {a} = Ideal.span {b * a} := by
    rw [← Submodule.singleton_set_smul]
    simp [← Ideal.submodule_span_eq, Submodule.set_smul_span]
  have := Module.length_eq_add_of_exact ((Ideal.mulQuot b (Ideal.span {a})).restrictScalars A)
    ((Ideal.quotOfMul b (Ideal.span {a})).restrictScalars A)
    (Ideal.mulQuot_injective (Ideal.span {a}) hb) (Ideal.quotOfMul_surjective (Ideal.span {a}))
    (Ideal.exact_mulQuot_quotOfMul (Ideal.span {a}))
  rw [hab, ← hI]
  exact this

/-- Proof: `length_quot_sup_span_mul` gives the `ℕ∞`-valued equation; the three lengths are finite by `hfl`
(`yy′ ∉ 𝔭` since `𝔭` is prime), and `ENat.toNat_add` concludes. -/
theorem lam_mul (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {y y' : B}
    (hy : y ∉ 𝔭) (hy' : y' ∉ 𝔭) : lam A 𝔭 (y * y') = lam A 𝔭 y + lam A 𝔭 y' := by
  unfold lam
  rw [length_quot_sup_span_mul 𝔭 hy', ENat.toNat_add (hfl y hy) (hfl y' hy')]

omit [𝔭.IsPrime] in
theorem lam_neg (y : B) : lam A 𝔭 (-y) = lam A 𝔭 y := by
  unfold lam; rw [Ideal.span_singleton_neg]

omit [𝔭.IsPrime] in
theorem lam_one : lam A 𝔭 (1 : B) = 0 := by
  unfold lam
  have h : 𝔭 ⊔ Ideal.span {(1 : B)} = ⊤ := by rw [Ideal.span_singleton_one, sup_top_eq]
  have : Subsingleton (B ⧸ (𝔭 ⊔ Ideal.span {(1 : B)})) := by
    rw [h]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Module.length_eq_zero]; rfl

theorem lam_pow (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {y : B}
    (hy : y ∉ 𝔭) (n : ℕ) : lam A 𝔭 (y ^ n) = n * lam A 𝔭 y := by
  induction n with
  | zero => rw [pow_zero, lam_one, Nat.zero_mul]
  | succ n ih =>
    rw [pow_succ, lam_mul 𝔭 hfl (fun h => hy (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)) hy, ih]
    ring

end KeyLemma

end
