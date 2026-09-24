import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.SumDefs
import MiyaokaMori.RingTheory.KeyLemma.ExactComplex
import MiyaokaMori.RingTheory.KeyLemma.HerbrandPi
import MiyaokaMori.RingTheory.KeyLemma.ToPiFiniteLength

/-! # Vanishing of the sum of the multiplicities `Hsym`

Let `A` be Noetherian local with `dim A ≤ 2`, `B` a normal domain finite over `A`, and `a, b ∈ B ∖ 0`.
Then at every `𝔭 ∈ MinPrimes(ab)` the cohomology of `(B/(abB_𝔭 ∩ B), a, b)` has finite length, and
`Σ_𝔭 e_A(B/(abB_𝔭 ∩ B), a, b) = 0`.

Reference: second paragraph of Stacks 0EAW ("Thus we see that Σ e_A(M_i, a, b) = 0 by Lemma 0EA9").
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]

/-- Proof, with `t := a * b`:
1. `herbrand_mulQ_span_mul`: the cohomology of `(B/t, a, b)` has finite length and `e = 0`.
2. `toPi_length_ne_top`: the kernel and cokernel of `toPi A t` have finite length; `toPi_comp_mulQ` says
   it commutes with multiplication by `a` and by `b`.
3. 0EA9, `PeriodicComplex.herbrand_eq_of_map (mulQ … a) (mulQ … b) (piMulQ A t a) (piMulQ A t b) (toPi A t)`;
   the four "is a complex" hypotheses are `mulQ_comp_eq_zero` (`a*b ∈ span`) and the same lemma
   componentwise (`a*b ∈ contr`, `span_le_contr`; `LinearMap.ext` + `funext`). This gives that the
   cohomology of the product complex has finite length and `e = 0`.
4. `PeriodicComplex.herbrand_pi` (`ι := MinPrimes t`, `finite_MinPrimes`; `piMulQ` is by definition the
   `LinearMap.pi` form of that lemma): each component has finite length and
   `0 = Σᶠ e(component) = Σᶠ Hsym A a b 𝔭.1` (`Hsym` unfolds by `rfl`).
Edge case: if `ab` is a unit then `MinPrimes` is empty and the sum is `0`. -/
theorem finsum_Hsym_eq_zero (hdim : ringKrullDim A ≤ 2) {a b : B} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ 𝔭 : MinPrimes (a * b),
        FiniteCohomology (mulQ A (contr 𝔭.1 (a * b)) a) (mulQ A (contr 𝔭.1 (a * b)) b)) ∧
      ∑ᶠ 𝔭 : MinPrimes (a * b), Hsym A a b 𝔭.1 = 0 := by
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  haveI : Finite (MinPrimes (a * b)) := finite_MinPrimes (a * b)
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  obtain ⟨hFC, hE⟩ := herbrand_mulQ_span_mul (A := A) ha hb
  obtain ⟨hK, hC⟩ := toPi_length_ne_top (A := A) hdim hab0
  have hmem : a * b ∈ Ideal.span {a * b} := Ideal.subset_span rfl
  have hpi : ∀ x y : B, x * y = a * b → piMulQ A (a * b) x ∘ₗ piMulQ A (a * b) y = 0 := by
    intro x y hxy
    refine LinearMap.ext fun m => funext fun 𝔭 => ?_
    have h := LinearMap.congr_fun (mulQ_comp_eq_zero (A := A) (x := x) (y := y) (contr 𝔭.1 (a * b))
      (by rw [hxy]; exact span_le_contr 𝔭.1 (a * b) hmem)) (m 𝔭)
    simpa [piMulQ] using h
  obtain ⟨hiff, heq⟩ := herbrand_eq_of_map (mulQ A (Ideal.span {a * b}) a)
    (mulQ A (Ideal.span {a * b}) b) (piMulQ A (a * b) a) (piMulQ A (a * b) b) (toPi A (a * b))
    (mulQ_comp_eq_zero _ hmem)
    (mulQ_comp_eq_zero (x := b) (y := a) _ (by rw [mul_comm b a]; exact hmem))
    (hpi a b rfl) (hpi b a (mul_comm b a)) (toPi_comp_mulQ _ a) (toPi_comp_mulQ _ b) hK hC
  have hFCpi := hiff.mp hFC
  have hEpi := heq hFC
  obtain ⟨hpiiff, hpisum⟩ := PeriodicComplex.herbrand_pi (R := A)
    (fun 𝔭 : MinPrimes (a * b) => mulQ A (contr 𝔭.1 (a * b)) a)
    (fun 𝔭 : MinPrimes (a * b) => mulQ A (contr 𝔭.1 (a * b)) b)
  have hall := hpiiff.mp hFCpi
  refine ⟨hall, ?_⟩
  have hsum := hpisum hall
  have hsum' : herbrand (piMulQ A (a * b) a) (piMulQ A (a * b) b)
      = ∑ᶠ 𝔭 : MinPrimes (a * b), Hsym A a b 𝔭.1 := hsum
  rw [← hsum', hEpi, hE]


end KeyLemma

end
