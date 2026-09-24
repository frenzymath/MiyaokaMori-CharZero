import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.SumDefs
import MiyaokaMori.RingTheory.Length.FiniteLengthOfSupport
import MiyaokaMori.RingTheory.KeyLemma.ToPiKernelLocal
import MiyaokaMori.RingTheory.KeyLemma.ToPiCokernelLocal

/-! # Finite length of the kernel and cokernel of the comparison map

`A` Noetherian local with `dim A ≤ 2`, `B` a normal domain finite over `A`, `t ≠ 0`: the kernel and
cokernel of the comparison map `B/tB → ∏_{𝔭 ∈ MinPrimes(t)} B/(tB_𝔭 ∩ B)` have finite `A`-length.

Reference: second paragraph of Stacks 0EAW ("whose kernel and cokernel are supported in {𝔪} and hence
have finite length").
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]

theorem finite_MinPrimes [IsNoetherianRing B] (t : B) : Finite (MinPrimes t) := by
  have := (Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {t})).to_subtype
  exact Finite.of_injective
    (fun 𝔭 : MinPrimes t => (⟨𝔭.1.asIdeal, 𝔭.2⟩ : (Ideal.span {t}).minimalPrimes))
    (fun x y h => Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val h)))

/-- Proof. Both conjuncts use `Module.length_ne_top_of_forall_exists_smul_eq_zero` (finiteness instances:
`Module.Finite A (B ⧸ I)` from `Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap`;
`Finite (MinPrimes t)` is `finite_MinPrimes`; `IsNoetherianRing B` from `IsNoetherianRing.of_finite A B`;
finiteness of submodules, products and quotients are Mathlib instances).
Kernel: `m = mk x ∈ Ker ⇒` every component `mk x = 0 ⇒ x ∈ contr 𝔭 t` (`Ideal.Quotient.eq_zero_iff_mem`);
`exists_smul_mem_span_of_forall_mem_contr` gives `s` with `s • mk x = mk (algebraMap A B s * x) = 0`
(`Algebra.smul_def`).
Cokernel: for `y`, choose representatives `x 𝔭` componentwise (`Ideal.Quotient.mk_surjective`);
`exists_smul_sub_mem_contr` gives `s`, `y₀` such that every component of `s • y − toPi (mk y₀)` is `0`,
hence `s • [y] = 0` (`Submodule.Quotient.mk_eq_zero`). -/
theorem toPi_length_ne_top (hdim : ringKrullDim A ≤ 2) {t : B} (ht : t ≠ 0) :
    Module.length A (LinearMap.ker (toPi A t)) ≠ ⊤ ∧
      Module.length A ((∀ 𝔭 : MinPrimes t, B ⧸ contr 𝔭.1 t) ⧸ LinearMap.range (toPi A t)) ≠ ⊤ := by
  classical
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  haveI : Finite (MinPrimes t) := finite_MinPrimes t
  haveI hq : ∀ I : Ideal B, Module.Finite A (B ⧸ I) := fun I =>
    Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A I).toLinearMap) Ideal.Quotient.mk_surjective
  constructor
  · refine Module.length_ne_top_of_forall_exists_smul_eq_zero _ ?_
    intro q hqp hqm m
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (m : B ⧸ Ideal.span {t})
    have hmem : ∀ 𝔭 : MinPrimes t, x ∈ contr 𝔭.1 t := by
      intro 𝔭
      have h0 : toPi A t (m : B ⧸ Ideal.span {t}) = 0 := m.2
      have := congrFun h0 𝔭
      rw [← hx] at this
      simpa only [toPi, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.factorₐ_apply_mk, Ideal.Quotient.eq_zero_iff_mem, Pi.zero_apply] using this
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem_span_of_forall_mem_contr hdim ht q hqm x hmem
    refine ⟨s, hs, ?_⟩
    refine Subtype.ext ?_
    show s • (m : B ⧸ Ideal.span {t}) = 0
    rw [← hx, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A B (B ⧸ Ideal.span {t}) s,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hsx
  · refine Module.length_ne_top_of_forall_exists_smul_eq_zero _ ?_
    intro q hqp hqm m
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ m
    choose x hx using fun 𝔭 : MinPrimes t => Ideal.Quotient.mk_surjective (y 𝔭)
    obtain ⟨s, hs, y₀, hy₀⟩ := exists_smul_sub_mem_contr hdim ht q hqm x
    refine ⟨s, hs, ?_⟩
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨Ideal.Quotient.mk (Ideal.span {t}) y₀, ?_⟩
    funext 𝔭
    have h1 := hy₀ 𝔭
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul] at h1
    simp only [toPi, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.factorₐ_apply_mk, Pi.smul_apply, Algebra.smul_def, ← hx 𝔭]
    rw [sub_eq_zero] at h1
    exact h1.symm ▸ rfl

end KeyLemma

end
