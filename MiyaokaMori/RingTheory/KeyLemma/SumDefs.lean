import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs

/-! # The comparison map of the Key Lemma

The comparison map `B/tB → ⊕_{𝔭 ∈ MinPrimes(t)} B/(tB_𝔭 ∩ B)` of the second paragraph of Stacks 0EAW
(`A/(ab) → ⊕ M_i` in the original): the index type `KeyLemma.MinPrimes t`, the `A`-linear map
`KeyLemma.toPi A t`, and its commutation with multiplication by `x`.

Reference: second paragraph of the proof of Stacks 0EAW ("Then we have a map A/(ab) → ⊕ M_i whose kernel
and cokernel are supported in {𝔪}").
-/

set_option autoImplicit false

universe u

noncomputable section

namespace KeyLemma

variable (A : Type u) {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The minimal primes of `(t)` (finitely many when `B` is Noetherian; for `B` a normal Noetherian domain and
`t ≠ 0` a nonunit, exactly the height-one primes containing `t`). -/
def MinPrimes (t : B) : Type u :=
  {𝔭 : PrimeSpectrum B // 𝔭.asIdeal ∈ (Ideal.span {t}).minimalPrimes}

theorem span_le_contr (𝔭 : PrimeSpectrum B) (t : B) : Ideal.span {t} ≤ contr 𝔭 t := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.subset_span rfl

/-- The comparison map `B/tB → ∏_{𝔭 ∈ MinPrimes t} B/(tB_𝔭 ∩ B)`. -/
def toPi (t : B) : (B ⧸ Ideal.span {t}) →ₗ[A] (∀ 𝔭 : MinPrimes t, B ⧸ contr 𝔭.1 t) :=
  LinearMap.pi fun 𝔭 => (Ideal.Quotient.factorₐ A (span_le_contr 𝔭.1 t)).toLinearMap

/-- Componentwise multiplication by `x`. -/
def piMulQ (t x : B) : (∀ 𝔭 : MinPrimes t, B ⧸ contr 𝔭.1 t) →ₗ[A] (∀ 𝔭 : MinPrimes t, B ⧸ contr 𝔭.1 t) :=
  LinearMap.pi fun 𝔭 => mulQ A (contr 𝔭.1 t) x ∘ₗ LinearMap.proj 𝔭

variable {A}

theorem toPi_comp_mulQ (t x : B) :
    toPi A t ∘ₗ mulQ A (Ideal.span {t}) x = piMulQ A t x ∘ₗ toPi A t := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
  funext 𝔭
  simp only [LinearMap.comp_apply, toPi, piMulQ, LinearMap.pi_apply, LinearMap.proj_apply, mulQ_apply,
    AlgHom.toLinearMap_apply, ← map_mul, Ideal.Quotient.factorₐ_apply_mk]

end KeyLemma

end
