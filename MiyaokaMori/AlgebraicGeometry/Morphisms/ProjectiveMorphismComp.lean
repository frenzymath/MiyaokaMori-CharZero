import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveQuasiProjectiveProper
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveComp
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveProperProjective

/-! # Composition of projective morphisms

A composition of projective morphisms is projective (for instance `Y_k^{GG}` is projective over
`C` and `C` is projective over `k`, hence `Y_k^{GG}` is projective over `k`; see §2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem IsProjectiveMorphism.comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsProjectiveMorphism f]
    [AlgebraicGeometry.IsProjectiveMorphism g] [CompactSpace Z] [QuasiSeparatedSpace Z] :
    AlgebraicGeometry.IsProjectiveMorphism (f ≫ g) := by
  have hf := AlgebraicGeometry.IsProjectiveMorphism.isQuasiProjective_isProper f
  have hg := AlgebraicGeometry.IsProjectiveMorphism.isQuasiProjective_isProper g
  have hfq : AlgebraicGeometry.IsQuasiProjectiveMorphism f := hf.1
  have hfp : AlgebraicGeometry.IsProper f := hf.2
  have hgq : AlgebraicGeometry.IsQuasiProjectiveMorphism g := hg.1
  have hgp : AlgebraicGeometry.IsProper g := hg.2
  have hfgq : AlgebraicGeometry.IsQuasiProjectiveMorphism (f ≫ g) :=
    AlgebraicGeometry.IsQuasiProjectiveMorphism.comp f g
  have hfgp : AlgebraicGeometry.IsProper (f ≫ g) := inferInstance
  exact AlgebraicGeometry.IsProjectiveMorphism.of_isQuasiProjective_isProper (f ≫ g)

end
