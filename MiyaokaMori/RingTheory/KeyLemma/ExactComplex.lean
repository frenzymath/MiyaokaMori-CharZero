import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs

/-! # Exactness of the periodic complex `(B/abB, a, b)`

For a domain `B` and `a, b ≠ 0`, the `(2,1)`-periodic complex `(B/abB, a, b)` is exact, so its
cohomology has finite length and `e_A = 0`.

Reference: second paragraph of the proof of Stacks 0EAW ("Since a, b are nonzerodivisors the
(2,1)-periodic complex (A/(ab), a, b) has vanishing cohomology").
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

/-- The cohomology `H(φ, ψ) = Ker φ / Im ψ` of a `2`-periodic complex is the zero module, of length `0`,
when `Ker φ ≤ Im ψ`. -/
theorem length_H_eq_zero_of_ker_le_range {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M)
    (h : LinearMap.ker φ ≤ LinearMap.range ψ) : Module.length R (H φ ψ) = 0 := by
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, Submodule.submoduleOf,
    Submodule.comap_subtype_eq_top]
  exact h

variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]

/-- For a domain `B` and `a ≠ 0`: on `B/abB`, `Ker(mult. by a) ≤ Im(mult. by b)`. `ax ∈ abB ⇒ ab ∣ ax ⇒ b ∣ x`
(cancel `a`). -/
theorem ker_mulQ_le_range_mulQ {a : B} (ha : a ≠ 0) (b : B) :
    LinearMap.ker (mulQ A (Ideal.span {a * b}) a) ≤
      LinearMap.range (mulQ A (Ideal.span {a * b}) b) := by
  intro m hm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [LinearMap.mem_ker, mulQ_apply, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, mul_dvd_mul_iff_left ha] at hm
  obtain ⟨y, rfl⟩ := hm
  exact ⟨Ideal.Quotient.mk _ y, by rw [mulQ_apply, ← map_mul]⟩

/-- Proof: `Ker(a : B/ab → B/ab) = bB/abB = Im(b)`: `ax ∈ abB ⇒ a(x − by) = 0 ⇒ x = by` (`a ≠ 0`, domain).
Symmetrically `Ker b = Im a`. Hence `H (mulQ a) (mulQ b)` and `H (mulQ b) (mulQ a)` are zero modules
(`Submodule.Quotient.subsingleton_iff` / `submoduleOf = ⊤`), `Module.length_eq_zero`; the two
`FiniteCohomology` conditions read `0 ≠ ⊤`, and `herbrand` unfolds to `0 − 0`. No finiteness is needed.
Edge cases: if `a` or `b` is a unit the corresponding kernel and image in `B/ab` still agree; likewise
for `a = b`. -/
theorem herbrand_mulQ_span_mul {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) :
    FiniteCohomology (mulQ A (Ideal.span {a * b}) a) (mulQ A (Ideal.span {a * b}) b) ∧
      herbrand (mulQ A (Ideal.span {a * b}) a) (mulQ A (Ideal.span {a * b}) b) = 0 := by
  have h1 : Module.length A (H (mulQ A (Ideal.span {a * b}) a) (mulQ A (Ideal.span {a * b}) b)) = 0 :=
    length_H_eq_zero_of_ker_le_range _ _ (ker_mulQ_le_range_mulQ ha b)
  have h2 : Module.length A (H (mulQ A (Ideal.span {a * b}) b) (mulQ A (Ideal.span {a * b}) a)) = 0 := by
    have := ker_mulQ_le_range_mulQ (A := A) hb a
    rw [mul_comm b a] at this
    exact length_H_eq_zero_of_ker_le_range _ _ this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h1]; exact ENat.zero_ne_top
  · rw [h2]; exact ENat.zero_ne_top
  · unfold herbrand; rw [h1, h2]; simp

end KeyLemma

end
