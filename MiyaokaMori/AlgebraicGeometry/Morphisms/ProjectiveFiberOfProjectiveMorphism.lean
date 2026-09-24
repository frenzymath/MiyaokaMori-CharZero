import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverIffProjectiveMorphism

/-! # Fibers of a projective morphism are projective over the residue field

If `f : Y ⟶ T` is projective and `t : T`, then `f.fiber t` is projective over `κ(t)`
(Stacks 01W6: projective morphisms are stable under base change; EGA II 5.5.5).

**Proof.** By definition `f.fiber t` is the pullback of `f` along `T.fromSpecResidueField t : Spec κ(t) ⟶ T`,
and its structure morphism `f.fiber t ↘ Spec κ(t)` is `pullback.snd f (T.fromSpecResidueField t)` (this is
the `Over` structure chosen by Mathlib's `Scheme.Hom.fiberOverSpecResidueField`). By
`IsProjectiveMorphism.baseChange f (T.fromSpecResidueField t)` this morphism is projective; the `mpr`
direction of `isProjectiveOver_iff_isProjectiveMorphism (T.residueField t) (f.fiber t)` converts this into
`IsProjectiveOver`. Since `CommRingCat.of ↥(T.residueField t)` and `T.residueField t` agree by definition,
the two lemmas compose directly.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The fiber of a projective morphism is projective over the residue field. -/
theorem AlgebraicGeometry.isProjectiveOver_fiber_of_isProjectiveMorphism
    {T Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ T)
    [AlgebraicGeometry.IsProjectiveMorphism f] (t : T) :
    letI := f.fiberOverSpecResidueField t
    IsProjectiveOver (T.residueField t) (f.fiber t) := by
  let _ := f.fiberOverSpecResidueField t
  exact (isProjectiveOver_iff_isProjectiveMorphism (T.residueField t) (f.fiber t)).mpr
    (AlgebraicGeometry.IsProjectiveMorphism.baseChange f (T.fromSpecResidueField t))


end
