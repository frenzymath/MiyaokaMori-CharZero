import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearLongExact
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopLinearEquiv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.SheafHPrimeInjectiveModule

/-! # Dimension shifting for sheaf cohomology

Let `0 → F → I → R → 0` be a short exact sequence of `O_X`-modules with `I` an injective
`O_X`-module. Then (all `Γ(X, O_X)`-linearly)
(a) `H^{p+1}(X, I) = 0`; (b) for `p ≥ 1` the connecting map `δ : H^p(X, R) → H^{p+1}(X, F)` is
bijective; (c) `H^1(X, F) ≃ Γ(X, R) / im(Γ(X, I) → Γ(X, R))`.

Proof: (a) injective modules are flasque (Stacks 09SX / Hartshorne III.2.4), flasque sheaves are
`H'`-acyclic, and `H'(⊤) ≃ H`; (b), (c) the linear long exact sequence together with (a); (c) also
uses the linear isomorphism `H^0 ≃ Γ` and its naturality.

Source: the end of the proof of Hartshorne III.4.5 ("comparing with the long exact sequence of
usual cohomology … using (2.5)").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Γ(X, ⊤)`-linear map induced by `φ` on global sections. -/
def Scheme.Modules.Hom.appTopLinear {M N : X.Modules} (φ : M ⟶ N) :
    Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤) :=
  (φ.val.app (Opposite.op ⊤)).hom

theorem Scheme.Modules.Hom.appTopLinear_apply {M N : X.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    Scheme.Modules.Hom.appTopLinear φ x = φ.app ⊤ x := rfl

/-- (a) Higher cohomology of an injective module vanishes. -/
theorem sheafCohomology.subsingleton_of_injective (I : X.Modules) [Injective I] (p : ℕ) :
    Subsingleton (sheafCohomology X I (p + 1)) :=
  have := Scheme.Modules.hPrime_subsingleton_of_injective I ⊤ (p + 1) (Nat.succ_pos p)
  (sheafCohomologyTopLinearEquiv I (p + 1)).symm.toEquiv.subsingleton

/-- (b) If the middle term is acyclic in degrees `n₀` and `n₁`, the connecting map `δ` is
bijective. -/
theorem sheafCohomology.δ_bijective {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    [Subsingleton (sheafCohomology X S.X₂ n₀)] [Subsingleton (sheafCohomology X S.X₂ n₁)] :
    Function.Bijective (sheafCohomology.δ hS n₀ n₁ h) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, ← sheafCohomology.range_map_g_eq_ker_δ hS n₀ n₁ h,
      LinearMap.range_eq_bot]
    exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]
  · rw [← LinearMap.range_eq_top, sheafCohomology.range_δ_eq_ker_map_f hS n₀ n₁ h,
      LinearMap.ker_eq_top]
    exact LinearMap.ext fun x => Subsingleton.elim _ _

/-- (c) If `H^1(X, I) = 0`, then `H^1(X, F) ≃ Γ(R) / im Γ(I)`. -/
theorem sheafCohomology.one_equiv_quotient {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Subsingleton (sheafCohomology X S.X₂ 1)] :
    Nonempty (sheafCohomology X S.X₁ 1 ≃ₗ[Γ(X, ⊤)]
      (Γ(S.X₃, ⊤) ⧸ LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g))) := by
  have hsurj : Function.Surjective (sheafCohomology.δ hS 0 1 rfl) := by
    rw [← LinearMap.range_eq_top, sheafCohomology.range_δ_eq_ker_map_f hS 0 1 rfl,
      LinearMap.ker_eq_top]
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  -- `δ ∘ e₃⁻¹ : Γ(R) → H^1(F)` is surjective with kernel `im Γ(I)`
  let e₂ := sheafCohomologyZeroEquiv S.X₂
  let e₃ := sheafCohomologyZeroEquiv S.X₃
  let d : Γ(S.X₃, ⊤) →ₗ[Γ(X, ⊤)] sheafCohomology X S.X₁ 1 :=
    (sheafCohomology.δ hS 0 1 rfl).comp e₃.symm.toLinearMap
  have hd : Function.Surjective d := hsurj.comp e₃.symm.surjective
  have hker : LinearMap.ker d = LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g) := by
    ext t
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    show sheafCohomology.δ hS 0 1 rfl (e₃.symm t) = 0 ↔ _
    rw [← LinearMap.mem_ker, ← sheafCohomology.range_map_g_eq_ker_δ hS 0 1 rfl, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨e₂ y, ?_⟩
      rw [Scheme.Modules.Hom.appTopLinear_apply, ← sheafCohomologyZeroEquiv_naturality, hy]
      exact e₃.apply_symm_apply t
    · rintro ⟨s, hs⟩
      refine ⟨e₂.symm s, e₃.injective ?_⟩
      rw [sheafCohomologyZeroEquiv_naturality, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, ← hs]
      rfl
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans (d.quotKerEquivOfSurjective hd)).symm⟩

end AlgebraicGeometry

end
