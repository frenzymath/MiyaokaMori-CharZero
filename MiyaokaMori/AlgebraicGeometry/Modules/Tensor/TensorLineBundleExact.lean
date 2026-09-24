import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence

/-! # Tensoring with a line bundle is exact

Tensoring with an invertible sheaf (line bundle) is an exact functor: a short exact sequence stays
short exact after tensoring with `L`.

Source: the proof of Stacks 0BEM ("Tensoring with the invertible module … is exact").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Instead of the local argument "`L ≅ O` locally", the proof uses the equivalence given by an
   invertible object (shorter, no local check): `L` is an invertible object of the monoidal category
   `X.Modules` (`L ⊗ L^∨ ≅ O_X`, Stacks 01CT), so `− ⊗ L` is a self-equivalence of `X.Modules`
   (`isEquivalence_tensorRight_of_isLineBundle`), hence preserves finite limits and colimits and zero
   morphisms, and sends short exact sequences to short exact sequences (Mathlib
   `ShortComplex.ShortExact.map_of_exact`). Take `T := S.map (− ⊗ L)`, the three isomorphisms the
   identities; the two compatibilities are `id_comp`/`comp_id`. -/

open scoped CategoryTheory.MonoidalCategory in
/-- Tensoring a short exact sequence `S` with a line bundle `L` gives a short exact sequence `T`
with `T.Xᵢ ≅ S.Xᵢ ⊗ L`, compatibly with the maps. -/
theorem AlgebraicGeometry.Scheme.Modules.shortExact_tensor_lineBundle {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact) :
    ∃ (T : CategoryTheory.ShortComplex X.Modules) (e₁ : T.X₁ ≅ S.X₁ ⊗ L) (e₂ : T.X₂ ≅ S.X₂ ⊗ L)
      (e₃ : T.X₃ ≅ S.X₃ ⊗ L),
      T.f ≫ e₂.hom = e₁.hom ≫ (S.f ▷ L) ∧ T.g ≫ e₃.hom = e₂.hom ≫ (S.g ▷ L) ∧ T.ShortExact := by
  have : (CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle L
  -- an equivalence preserves empty colimits ⇒ zero objects ⇒ zero morphisms (needed by
  -- `ShortComplex.map` and `map_of_exact`)
  have : CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete PEmpty.{1})
      (CategoryTheory.MonoidalCategory.tensorRight L) := inferInstance
  have : (CategoryTheory.MonoidalCategory.tensorRight L).PreservesZeroMorphisms := inferInstance
  refine ⟨S.map (CategoryTheory.MonoidalCategory.tensorRight L), Iso.refl _, Iso.refl _,
    Iso.refl _, ?_, ?_, hS.map_of_exact (CategoryTheory.MonoidalCategory.tensorRight L)⟩
  · show (S.f ▷ L) ≫ 𝟙 _ = 𝟙 _ ≫ (S.f ▷ L)
    rw [Category.comp_id, Category.id_comp]
  · show (S.g ▷ L) ≫ 𝟙 _ = 𝟙 _ ≫ (S.g ▷ L)
    rw [Category.comp_id, Category.id_comp]

end
