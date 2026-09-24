import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow

/-! # Sections of a finite biproduct

**Sections of a finite biproduct of `O_X`-modules are the product of the sections.**
For `J` finite and `M : J → X.Modules`, the map `Γ(U, ⨁_j M_j) → ∏_j Γ(U, M_j)`, `x ↦ (π_j x)_j`, is bijective
(for every open `U`, no quasi-coherence needed).

Proof: elementwise from the biproduct identities. `biproduct.total` (`Σ_j π_j ≫ ι_j = 𝟙`) evaluated on a section
gives `x = Σ_j ι_j (π_j x)` (a finite sum of morphisms acts on sections as the sum of the actions), whence
injectivity; for `v = (v_j)_j` the section `x := Σ_k ι_k (v_k)` has `π_j x = v_j` by `biproduct.ι_π_self` /
`biproduct.ι_π_ne`, whence surjectivity. (`X.Modules` has finite biproducts: `Modules.hasFiniteBiproducts`.)

Used for the graded pieces of the weighted symmetric algebra (`Γ(U, S.part m) = ⨁_{d ∈ D_m} Γ(U, T_d)`).
Reference: standard (Stacks 009F, sections of finite products of sheaves; here a formal consequence of the
biproduct axioms since `Γ(U, -)` is additive).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A finite sum of morphisms of `O_X`-modules acts on a section as the sum of the actions. -/
theorem Hom.finset_sum_app_apply {M N : X.Modules} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N))
    (U : X.Opens) (x : Γ(M, U)) :
    (∑ i ∈ s, f i).app U x = ∑ i ∈ s, (f i).app U x := by
  let F : (M ⟶ N) →+ Γ(N, U) :=
    { toFun := fun φ => φ.app U x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum F f s

/-- `biproduct.total` on sections: `x = Σ_j ι_j (π_j x)`. -/
theorem biproduct_sections_total {J : Type} [Fintype J] (M : J → X.Modules) (U : X.Opens)
    (x : Γ(⨁ M, U)) :
    x = ∑ j, (CategoryTheory.Limits.biproduct.ι M j).app U
      ((CategoryTheory.Limits.biproduct.π M j).app U x) := by
  have h := congrArg (fun φ : (⨁ M ⟶ ⨁ M) => φ.app U x) (CategoryTheory.Limits.biproduct.total (f := M))
  simp only at h
  rw [Hom.finset_sum_app_apply] at h
  exact h.symm

/-- `π_j (ι_j v) = v` on sections. -/
theorem biproduct_π_ι_self_app_apply {J : Type} [Fintype J] (M : J → X.Modules) (U : X.Opens) (j : J)
    (v : Γ(M j, U)) :
    (CategoryTheory.Limits.biproduct.π M j).app U ((CategoryTheory.Limits.biproduct.ι M j).app U v) = v :=
  congrArg (fun φ : (M j ⟶ M j) => φ.app U v) (CategoryTheory.Limits.biproduct.ι_π_self M j)

/-- `π_j (ι_k v) = 0` on sections for `k ≠ j`. -/
theorem biproduct_π_ι_ne_app_apply {J : Type} [Fintype J] (M : J → X.Modules) (U : X.Opens) {j k : J}
    (h : k ≠ j) (v : Γ(M k, U)) :
    (CategoryTheory.Limits.biproduct.π M j).app U ((CategoryTheory.Limits.biproduct.ι M k).app U v) = 0 :=
  congrArg (fun φ : (M k ⟶ M j) => φ.app U v) (CategoryTheory.Limits.biproduct.ι_π_ne M h)

/-- **Sections of a finite biproduct**: `x ↦ (π_j x)_j` is a bijection `Γ(U, ⨁ M) → ∏ Γ(U, M j)`. -/
theorem biproduct_sections_bijective {J : Type} [Fintype J] (M : J → X.Modules) (U : X.Opens) :
    Function.Bijective (fun x : Γ(⨁ M, U) => fun j : J =>
      (CategoryTheory.Limits.biproduct.π M j).app U x) := by
  classical
  refine ⟨fun x y hxy => ?_, fun v => ?_⟩
  · rw [biproduct_sections_total M U x, biproduct_sections_total M U y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (CategoryTheory.Limits.biproduct.π M j).app U x =
        (CategoryTheory.Limits.biproduct.π M j).app U y := congrFun hxy j
    rw [hj]
  · refine ⟨∑ k, (CategoryTheory.Limits.biproduct.ι M k).app U (v k), ?_⟩
    funext j
    show (CategoryTheory.Limits.biproduct.π M j).app U
      (∑ k, (CategoryTheory.Limits.biproduct.ι M k).app U (v k)) = v j
    rw [map_sum, Finset.sum_eq_single j]
    · exact biproduct_π_ι_self_app_apply M U j (v j)
    · intro k _ hk
      exact biproduct_π_ι_ne_app_apply M U hk (v k)
    · intro hj
      exact absurd (Finset.mem_univ j) hj

end AlgebraicGeometry.Scheme.Modules

end
