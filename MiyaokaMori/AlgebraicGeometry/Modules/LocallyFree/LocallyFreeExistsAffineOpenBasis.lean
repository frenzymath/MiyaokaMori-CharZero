import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames

/-! # Affine opens on which a locally free sheaf is free

A locally free sheaf of finite type has, around every point, an **affine** open `U` on which its
sections form a free `Γ(X, U)`-module of finite rank: `∃ U ∈ affineOpens, I finite, x ∈ U,
Module.Basis I Γ(X, U) Γ(W, U)`.

Proof: `MiyaokaMori.DualPullback.exists_frame` gives an open `U ∋ x`, a finite `I` and a frame
`e : I → Γ(W, U)` (on every `V ≤ U` the map `(I → Γ(X, V)) → Γ(W, V)`, `r ↦ ∑ rᵢ • eᵢ|_V` is
bijective). Affine opens form a basis of the topology (`isBasis_affineOpens`), so there is an affine
`V` with `x ∈ V ≤ U`; the frame restricted to `V` gives the linear equivalence
`frameEquiv : (I → Γ(X, V)) ≃ₗ Γ(W, V)`, and `Module.Basis.ofEquivFun` turns its inverse into a basis.

Source: Stacks 01C6 (locally free of finite rank), Hartshorne II.5 (Exercise 5.18 (b)–(c)).
Used for `Omega_totalSpace_iso_pullback_dual`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Around every point, a locally free sheaf of finite type has an affine open on which its sections
are a free module of finite rank. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_affineOpen_basis_sections
    {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules) [W.IsLocallyFree] [W.IsFiniteType] (x : X) :
    ∃ (U : X.affineOpens) (I : Type u) (_ : Finite I), x ∈ U.1 ∧
      Nonempty (Module.Basis I Γ(X, U.1) Γ(W, U.1)) := by
  obtain ⟨U, I, hI, e, hxU, he⟩ := MiyaokaMori.DualPullback.exists_frame W x
  let _ := hI
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  have hVU' : V ≤ U := hVU
  exact ⟨⟨V, hV⟩, I, Finite.of_fintype I, hxV,
    ⟨Module.Basis.ofEquivFun (MiyaokaMori.DualPullback.frameEquiv he hVU').symm⟩⟩

end
