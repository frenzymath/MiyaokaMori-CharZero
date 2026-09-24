import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Length.PeriodicComplexLength
import Mathlib.Data.ENat.BigOperators

/-! # Herbrand quotient of a finite product of periodic complexes

For a finite product of `(2,1)`-periodic complexes: the cohomology has finite length iff every factor
does, and `e(∏) = Σ e`.

Reference: the special case of Stacks 0EA7 (chow-lemma-additivity-periodic-length) for split short exact
sequences; used in the second paragraph of 0EAW ("`Σ e_A(M_i, a, b) = 0`").
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace PeriodicComplex

section Pi

variable {R : Type*} [Ring R] {ι : Type*} {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (φ : ∀ i, M i →ₗ[R] N i) (ψ : ∀ i, N i →ₗ[R] M i)

/-- The map `Ker (∏ φ) → ∏ H(φ i, ψ i)` of the product complex: componentwise residue class. -/
def kerPiToPiH :
    ↥(LinearMap.ker (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i)) →ₗ[R] ∀ i, H (φ i) (ψ i) :=
  LinearMap.pi fun i => (Submodule.mkQ _) ∘ₗ
    LinearMap.codRestrict (LinearMap.ker (φ i))
      (LinearMap.proj i ∘ₗ (LinearMap.ker (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i)).subtype)
      (fun x => by
        have hx := x.2
        rw [LinearMap.mem_ker] at hx ⊢
        have := congr_fun hx i
        simpa using this)

theorem kerPiToPiH_apply
    (x : ↥(LinearMap.ker (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i))) (i : ι) :
    kerPiToPiH φ ψ x i = Submodule.Quotient.mk
      (⟨(x : ∀ i, M i) i, by
        have hx := x.2
        rw [LinearMap.mem_ker] at hx ⊢
        simpa using congr_fun hx i⟩ : LinearMap.ker (φ i)) := rfl

theorem kerPiToPiH_surjective : Function.Surjective (kerPiToPiH φ ψ) := by
  intro y
  choose z hz using fun i => Submodule.mkQ_surjective _ (y i)
  refine ⟨⟨fun i => (z i : M i), ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker]
    funext i
    simp
  · funext i
    rw [kerPiToPiH_apply]
    exact hz i

theorem ker_kerPiToPiH :
    LinearMap.ker (kerPiToPiH φ ψ) =
      (LinearMap.range (LinearMap.pi fun i => ψ i ∘ₗ LinearMap.proj i)).submoduleOf
        (LinearMap.ker (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i)) := by
  ext x
  have hiff : ∀ i, kerPiToPiH φ ψ x i = 0 ↔ ∃ w, ψ i w = (x : ∀ i, M i) i := fun i => by
    rw [kerPiToPiH_apply, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf,
      Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
  rw [LinearMap.mem_ker, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.mem_range, funext_iff]
  simp only [Pi.zero_apply, hiff]
  constructor
  · intro h
    choose w hw using h
    exact ⟨w, funext fun i => by simpa using hw i⟩
  · rintro ⟨w, hw⟩ i
    exact ⟨w i, by simpa using congr_fun hw i⟩

/-- `H(∏ φ, ∏ ψ) ≃ ∏ H(φ i, ψ i)`. -/
def HPiEquiv :
    H (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i) (LinearMap.pi fun i => ψ i ∘ₗ LinearMap.proj i)
      ≃ₗ[R] ∀ i, H (φ i) (ψ i) :=
  (Submodule.quotEquivOfEq _ _ (ker_kerPiToPiH φ ψ).symm).trans
    ((kerPiToPiH φ ψ).quotKerEquivOfSurjective (kerPiToPiH_surjective φ ψ))

theorem length_H_pi [Fintype ι] :
    Module.length R (H (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i)
        (LinearMap.pi fun i => ψ i ∘ₗ LinearMap.proj i)) =
      ∑ i, Module.length R (H (φ i) (ψ i)) := by
  rw [(HPiEquiv φ ψ).length_eq, Module.length_pi_of_fintype]

end Pi

end PeriodicComplex

/-- Proof: `kerPiToPiH` (`Ker(∏φ) → ∏ H(φ i, ψ i)`, componentwise residue class) is surjective with kernel
`(Im ∏ψ) ∩ Ker(∏φ)`, so `H (∏φ) (∏ψ) ≃ₗ[R] ∀ i, H (φ i) (ψ i)` (`HPiEquiv`);
`Module.length_pi_of_fintype` gives `length = Σ length`; `ENat.sum_ne_top` gives "finite sum `≠ ⊤` ⟺ all
terms `≠ ⊤`"; `ENat.toNat_sum` gives additivity of `toNat` on finite sums. Edge case `ι` empty: both
sides are `0`. -/
theorem PeriodicComplex.herbrand_pi {R : Type*} [Ring R] {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (φ ψ : ∀ i, M i →ₗ[R] M i) :
    (FiniteCohomology (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i)
        (LinearMap.pi fun i => ψ i ∘ₗ LinearMap.proj i) ↔ ∀ i, FiniteCohomology (φ i) (ψ i)) ∧
      ((∀ i, FiniteCohomology (φ i) (ψ i)) →
        herbrand (LinearMap.pi fun i => φ i ∘ₗ LinearMap.proj i)
          (LinearMap.pi fun i => ψ i ∘ₗ LinearMap.proj i) = ∑ᶠ i, herbrand (φ i) (ψ i)) := by
  cases nonempty_fintype ι
  have h0 := length_H_pi φ ψ
  have h1 := length_H_pi ψ φ
  refine ⟨?_, ?_⟩
  · simp only [FiniteCohomology, h0, h1, ENat.sum_ne_top, Finset.mem_univ, true_implies, forall_and]
  · intro hfin
    simp only [herbrand, h0, h1, finsum_eq_sum_of_fintype]
    rw [ENat.toNat_sum (fun i _ => (hfin i).1), ENat.toNat_sum (fun i _ => (hfin i).2)]
    push_cast
    rw [Finset.sum_sub_distrib]

end
