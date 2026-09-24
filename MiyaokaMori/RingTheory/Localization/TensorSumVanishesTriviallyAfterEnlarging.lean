import MiyaokaMori.Prelude

/-! # A vanishing sum of tensors vanishes trivially after enlarging the family

Let `R` be a commutative ring, `N`, `P` `R`-modules, `n : ι → N`, `p : ι → P` finite families with
`∑ᵢ nᵢ ⊗ pᵢ = 0` (in `N ⊗_R P`). Then there are finitely many additional elements `n' : Fin k → N` such
that the enlarged families `(n, n')`, `(p, 0)` "vanish trivially" (Mathlib's `TensorProduct.VanishesTrivially`,
the equational criterion of Stacks 00HK): there are `y : Fin l → P` and coefficients `a` with
`pᵢ = ∑ⱼ a(i,j) yⱼ`, `0 = ∑ⱼ a(k,j) yⱼ`, and for every `j`, `∑ᵢ a(i,j) nᵢ + ∑ₖ a(k,j) n'ₖ = 0`. `N` need not
be finitely generated.

Proof:
1. Let `N₀ = span(range n)` (finitely generated), `x = ∑ᵢ ⟨nᵢ⟩ ⊗ pᵢ ∈ N₀ ⊗ P`; the image of `x` in `N ⊗ P`
   is `∑ nᵢ ⊗ pᵢ = 0`.
2. Every module is the directed limit of its finitely generated submodules, and tensor products commute with
   directed limits (Mathlib `Submodule.FG.exists_rTensor_fg_inclusion_eq`): there is a finitely generated
   submodule `N' ≥ N₀` such that the image of `x` in `N' ⊗ P` is already `0`.
3. Take finitely many generators `g : Fin k → N'` of `N'` (`Module.Finite.exists_fin`); the family
   `(incl nᵢ, gₖ)` generates `N'`, and `∑ incl(nᵢ) ⊗ pᵢ + ∑ gₖ ⊗ 0 = 0`.
4. Apply the forward direction of the equational criterion to the generating family (Mathlib
   `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero`) to get trivial-vanishing data in `N'`; push the
   relations `∑ a • m = 0` along the inclusion `N' ↪ N` to conclude (`n'ₖ :=` the image of `gₖ`).

Reference: the equational criterion Stacks 00HK together with the reduction to finitely generated submodules
(as in 04VX); Mathlib `LinearAlgebra/TensorProduct/Vanishing`, `Algebra/Colimit/TensorProduct`.
-/

set_option autoImplicit false

open TensorProduct

theorem TensorProduct.exists_vanishesTrivially_sumElim_of_sum_tmul_eq_zero
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P] {ι : Type*} [Fintype ι]
    (n : ι → N) (p : ι → P) (h : ∑ i, n i ⊗ₜ[R] p i = 0) :
    ∃ (k : ℕ) (n' : Fin k → N),
      TensorProduct.VanishesTrivially R (Sum.elim n n') (Sum.elim p (fun _ : Fin k ↦ (0 : P))) := by
  classical
  let N₀ : Submodule R N := Submodule.span R (Set.range n)
  have hN₀ : N₀.FG := Submodule.fg_span (Set.finite_range n)
  let n₀ : ι → N₀ := fun i ↦ ⟨n i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hx : N₀.subtype.rTensor P (∑ i, n₀ i ⊗ₜ[R] p i) = N₀.subtype.rTensor P 0 := by
    simpa [n₀] using h
  obtain ⟨N', hN', hle, hx'⟩ := hN₀.exists_rTensor_fg_inclusion_eq hx
  have : Module.Finite R N' := Module.Finite.iff_fg.mpr hN'
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := N')
  let m : ι ⊕ Fin k → N' := Sum.elim (fun i ↦ N₀.inclusion hle (n₀ i)) g
  have hm : Submodule.span R (Set.range m) = ⊤ := by
    rw [eq_top_iff, ← hg]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inr j, rfl⟩
  have hsum : ∑ s, m s ⊗ₜ[R] (Sum.elim p (fun _ : Fin k ↦ (0 : P))) s = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, tmul_zero, Finset.sum_const_zero, add_zero, m]
    simpa only [map_sum, LinearMap.rTensor_tmul, map_zero] using hx'
  obtain ⟨l, a, y, h₁, h₂⟩ := TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero R hm hsum
  refine ⟨k, fun j ↦ (g j : N), l, a, y, h₁, fun j ↦ ?_⟩
  have := congrArg N'.subtype (h₂ j)
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rcases s with i | j' <;> rfl
