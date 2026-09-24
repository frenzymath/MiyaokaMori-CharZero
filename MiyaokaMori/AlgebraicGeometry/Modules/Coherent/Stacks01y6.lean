import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pbAffineOpen
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01lc

/-! # Pushforward along a finite morphism preserves coherence (Stacks 01Y6)

For `f` finite, `Y` locally Noetherian and `F` coherent, `f_*F` is coherent (closed immersions are
finite morphisms).

Stacks 01Y6 (`coherent-lemma-finite-pushforward-coherent`), the `R^0 f_*` part: for a finite morphism
`f : X → Y` and a coherent `M` on `X`, the pushforward `f_*M` is coherent. With the definition
`IsCoherent = IsQuasicoherent ∧ IsFiniteType` the argument does not use that `Y` is locally
Noetherian; the hypothesis is kept in the statement to match the source (whose statement also asserts
`R^p f_* M = 0` for `p > 0`, which is not needed here).

Proof (all pieces at the variable level, no concrete constants, so the kernel check is fast):
1. `f` finite ⇒ `f` affine ⇒ quasi-compact and (separated, hence) quasi-separated, so `f_*M` is
   quasi-coherent by Stacks 01LC (`isQuasicoherent_pushforward`).
2. Finite type is checked on affine opens of `Y` (`isFiniteType_of_finite_affine_sections`): for an
   affine open `V ⊆ Y`,
   `Γ(f_*M, V) = Γ(M, f⁻¹V)` (definition of the pushforward, `pushforward_obj_obj`), `f⁻¹V` is affine
   (`IsAffineOpen.preimage`, `f` affine), `Γ(M, f⁻¹V)` is a finite `Γ(X, f⁻¹V)`-module (Stacks 01PB "⇒",
   `finite_sections_of_isFiniteType`), and `Γ(Y, V) → Γ(X, f⁻¹V)` is finite (Mathlib `IsFinite.finite_app`);
   transitivity of module-finiteness (Stacks 00GJ, Mathlib `Module.Finite.trans`) gives that
   `Γ(f_*M, V)` is a finite `Γ(Y, V)`-module.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Affine-local half of Stacks 01Y6: `f : X → Y` finite, `M` quasi-coherent of finite type on `X`,
`V ⊆ Y` affine open. Then `Γ(f_*M, V)` — by definition of `Scheme.Modules.pushforward` the module
`Γ(M, f ⁻¹ᵁ V)` with `Γ(Y, V)` acting through `f.app V : Γ(Y, V) → Γ(X, f ⁻¹ᵁ V)` — is a finite
`Γ(Y, V)`-module.

Proof: `f ⁻¹ᵁ V` is affine (`IsAffineOpen.preimage`, `f` is an affine morphism), so `Γ(M, f ⁻¹ᵁ V)` is a
finite `Γ(X, f ⁻¹ᵁ V)`-module (Stacks 01PB, `finite_sections_of_isFiniteType`); `f.app V` is a finite ring
map (`IsFinite.finite_app`); the `Γ(Y, V)`-action on `Γ(f_*M, V)` is `Module.compHom` along `f.app V`,
which makes `Γ(Y, V) → Γ(X, f ⁻¹ᵁ V) → Γ(M, f ⁻¹ᵁ V)` a scalar tower, and `Module.Finite.trans`
(Stacks 00GJ) concludes. No Noetherian hypothesis is needed. -/
theorem AlgebraicGeometry.Scheme.Modules.finite_sections_pushforward_of_isFinite
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (V : Y.Opens)
    (hV : AlgebraicGeometry.IsAffineOpen V) :
    Module.Finite Γ(Y, V) Γ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj M, V) := by
  have hfin : (f.app V).hom.Finite := AlgebraicGeometry.IsFinite.finite_app f V hV
  have hM : Module.Finite Γ(X, f ⁻¹ᵁ V) Γ(M, f ⁻¹ᵁ V) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_isFiniteType M (hV.preimage f)
  let _ : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let _ : Module Γ(Y, V) Γ(M, f ⁻¹ᵁ V) := Module.compHom _ (f.app V).hom
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(M, f ⁻¹ᵁ V) :=
    ⟨fun r a m => by
      change ((f.app V).hom r * a) • m = (f.app V).hom r • (a • m)
      rw [mul_smul]⟩
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hfin
  have h := Module.Finite.trans (R := Γ(Y, V)) Γ(X, f ⁻¹ᵁ V) Γ(M, f ⁻¹ᵁ V)
  exact h

/-- **Stacks 01Y6** (`R^0 f_*` part): the pushforward of a coherent module along a finite morphism is
coherent. Quasi-coherence is Stacks 01LC (`isQuasicoherent_pushforward`); finite type is checked on
the affine opens of `Y` with
`isFiniteType_of_finite_affine_sections` and `finite_sections_pushforward_of_isFinite`. The hypothesis
`IsLocallyNoetherian Y` is not used (kept to match the source statement). -/
theorem AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f]
    [AlgebraicGeometry.IsLocallyNoetherian Y] (M : X.Modules) [M.IsCoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj M).IsCoherent := by
  have : M.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have : M.IsFiniteType := AlgebraicGeometry.Scheme.Modules.IsCoherent.finiteType
  have hqc : ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward f M
  refine ⟨hqc, ?_⟩
  apply AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections
  intro y
  obtain ⟨V, hV, hy, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show y ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨V, hV, hy,
    AlgebraicGeometry.Scheme.Modules.finite_sections_pushforward_of_isFinite f M V hV⟩

end
