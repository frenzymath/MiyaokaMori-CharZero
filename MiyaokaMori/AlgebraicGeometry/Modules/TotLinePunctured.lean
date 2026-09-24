import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedImmersionOpenComplement
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedImmersionOpenComplement
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionOfSeparatedIsClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection

/-! # The punctured total space of a line bundle

The punctured total space `Tot(L)^× = Tot(L)` minus the zero section (the model of `Z^×`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.Scheme.totalSpacePunctured {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] : (AlgebraicGeometry.Scheme.totalSpace V).left.Opens :=
  -- Tot(V) → X is a relative Spec, hence affine, hence separated (`IsSeparated.of_isAffineHom`)
  haveI : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.totalSpace V).hom :=
    AlgebraicGeometry.Scheme.relativeSpec_isAffineHom _
  haveI : AlgebraicGeometry.IsClosedImmersion (AlgebraicGeometry.Scheme.zeroSection V) :=
    AlgebraicGeometry.IsClosedImmersion.of_section (AlgebraicGeometry.Scheme.totalSpace V).hom
      (AlgebraicGeometry.Scheme.zeroSection V)
      (AlgebraicGeometry.Scheme.zeroSection_comp V)  -- the zero section is a section of Tot(V) → X
  AlgebraicGeometry.Scheme.complementOfClosedImmersion (AlgebraicGeometry.Scheme.zeroSection V)

end
