import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismImageAsRange

/-! # The image of a morphism from a proper scheme is closed

From `C → Spec k` universally closed and `X → Spec k` separated, `f : C ⟶ X` is universally closed,
hence a closed map, so its image is closed (Theorem 1.1 of the paper: the image `f(C)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.Hom.isClosed_setImage {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.UniversallyClosed (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsSeparated (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (f : C ⟶ X) (hf : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))) :
    IsClosed f.setImage := by
  haveI := hf
  -- hf : f ≫ (X ↘ Spec k) = C ↘ Spec k (`CategoryTheory.comp_over`); the latter is universally closed
  haveI : AlgebraicGeometry.UniversallyClosed (f ≫ X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.comp_over f (AlgebraicGeometry.Spec (CommRingCat.of k))]
    infer_instance
  haveI : AlgebraicGeometry.UniversallyClosed f :=
    .of_comp_of_isSeparated f (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  simpa [AlgebraicGeometry.Scheme.Hom.setImage, ← Set.image_univ]
    using f.isClosedMap _ isClosed_univ

end
