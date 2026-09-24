import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf

/-! # The twisting sheaf of `Proj` on a basic open set

Description of the twisting sheaf of `Proj A` on a standard open set (Stacks 01M7, 01MN, 01MK):
for `f` homogeneous of positive degree, under `D₊(f) ≅ Spec A_(f)` the restriction `O(k)|_{D₊(f)}`
is the quasi-coherent sheaf associated with the `A_(f)`-module `(A_f)_k` (the degree-`k` part of
`A_f`), and the multiplication `O(a) ⊗ O(b) → O(a+b)` corresponds to
`(A_f)_a ⊗ (A_f)_b → (A_f)_{a+b}`. This module provides the degree-`k` part `(A_f)_k`
(see Lemma 2.2 of the paper for the role of `O(m)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree-`k` part of `A_f` (for `f ∈ 𝒜 m`, `m > 0`): the elements of the form `a / f^j` with
`a ∈ 𝒜 i` and `i = j·m + k`, as an `A_(f)`-submodule of `Localization.Away f`
(where `A_(f) = HomogeneousLocalization.Away 𝒜 f` acts through `val`). -/
noncomputable def AlgebraicGeometry.Proj.awayDegreePart {σ A : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (k : ℤ) : ModuleCat.{u} (HomogeneousLocalization.Away 𝒜 f) :=
  ModuleCat.of _ (Submodule.span (HomogeneousLocalization.Away 𝒜 f)
    {x : Localization.Away f | ∃ (i j : ℕ) (a : A), a ∈ 𝒜 i ∧ (i : ℤ) = j * m + k ∧
      x = Localization.mk a (⟨f ^ j, j, rfl⟩ : Submonoid.powers f)})

end
