import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # Morphisms between projective varieties are proper

A `k`-morphism between projective `k`-varieties is proper (the pushforward `f_*[C]` requires `f`
to be proper); this is part of the standing conventions of §1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Projective implies proper structure morphism (`IsProjectiveOver.isProper`: a closed immersion
   composed with `P^N ↘ Spec k` is proper); then `f ≫ (Y ↘ k) = X ↘ k` is proper and `Y ↘ k` is
   separated, so `f` is proper (`IsProper.of_comp`). -/

instance isProper_of_projective {k : Type u} [Field k] {X Y : SmoothProjectiveVariety k}
    (f : X.toScheme ⟶ Y.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    AlgebraicGeometry.IsProper f := by
  have : AlgebraicGeometry.IsProper (Y.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper Y.projective
  have : AlgebraicGeometry.IsProper (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper X.projective
  have hf : f ≫ (Y.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    (inferInstance : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1
  have : AlgebraicGeometry.IsProper (f ≫ Y.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [hf]
    infer_instance
  exact AlgebraicGeometry.IsProper.of_comp f (Y.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

end
