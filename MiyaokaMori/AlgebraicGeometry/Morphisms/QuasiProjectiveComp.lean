import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0c4k

/-! # Composition of quasi-projective morphisms

A composition of quasi-projective morphisms with quasi-compact target is quasi-projective
(Stacks Project, Tag 0C4M).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks Project, Tag 0C4M: a composition of quasi-projective morphisms is quasi-projective when the
target `S` is quasi-compact.

Proof (Stacks 0C4M):
1. Locally of finite type and quasi-compact are both stable under composition (Mathlib's
   `MorphismProperty.IsStableUnderComposition` instances for `@LocallyOfFiniteType` and
   `@QuasiCompact`), so `f ≫ g` is locally of finite type and quasi-compact.
2. Take an `f`-relatively ample line bundle `L` and a `g`-relatively ample line bundle `M` (the third
   field of `IsQuasiProjectiveMorphism`).
3. Stacks 0C4K (`exists_relativelyAmple_tensor_pullback_tensorPow_comp`): with `S`, `f`, `g`
   quasi-compact there is `a₀` such that for all `a ≥ a₀` the bundle `L ⊗ f^*(M^{⊗a})` is relatively
   ample for `f ≫ g`; take `a = a₀`.
4. `L ⊗ f^*(M^{⊗a₀})` is a line bundle (`IsLineBundle.tensor`, `.pullback`, `.tensorPow`) and
   witnesses `exists_relativelyAmple`. -/
theorem AlgebraicGeometry.IsQuasiProjectiveMorphism.comp {X Y S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [AlgebraicGeometry.IsQuasiProjectiveMorphism f]
    [AlgebraicGeometry.IsQuasiProjectiveMorphism g] [CompactSpace S] :
    AlgebraicGeometry.IsQuasiProjectiveMorphism (f ≫ g) := by
  have hf := AlgebraicGeometry.IsQuasiProjectiveMorphism.locallyOfFiniteType (f := f)
  have hg := AlgebraicGeometry.IsQuasiProjectiveMorphism.locallyOfFiniteType (f := g)
  have qf := AlgebraicGeometry.IsQuasiProjectiveMorphism.quasiCompact (f := f)
  have qg := AlgebraicGeometry.IsQuasiProjectiveMorphism.quasiCompact (f := g)
  obtain ⟨L, hL, hLamp⟩ := AlgebraicGeometry.IsQuasiProjectiveMorphism.exists_relativelyAmple (f := f)
  obtain ⟨M, hM, hMamp⟩ := AlgebraicGeometry.IsQuasiProjectiveMorphism.exists_relativelyAmple (f := g)
  obtain ⟨a₀, ha⟩ := AlgebraicGeometry.exists_relativelyAmple_tensor_pullback_tensorPow_comp
    f g L M hLamp hMamp
  refine ⟨MorphismProperty.comp_mem _ f g hf hg, MorphismProperty.comp_mem _ f g qf qg, ?_⟩
  exact ⟨_, inferInstance, ha a₀ le_rfl⟩

end
