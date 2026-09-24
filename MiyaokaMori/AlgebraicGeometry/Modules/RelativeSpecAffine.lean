import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec

/-! # The relative Spec is affine over the base

`Spec_X A ⟶ X` is an affine morphism; for an affine open `U`, `π⁻¹(U) ≅ Spec A(U)` (Stacks 01LX(1)(3)).
Used for the total space of a vector bundle (affine over the base) and for the jet schemes
`J_k^s = Spec_C S`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

instance AlgebraicGeometry.Scheme.relativeSpec_isAffineHom {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.relativeSpec A).hom :=
  -- `AffineAlgebra.relativeSpec_isAffineHom`
  A.toAffineAlgebra.relativeSpec_isAffineHom

/-- Stacks 01LX(3): the relative Spec over an affine open is the Spec of the ring of sections;
    `A.sectionsRing U` is the ring of sections over `U` of the quasi-coherent sheaf of algebras.
    Construction: `AffineAlgebra.chart_isPullback` says that `Spec A(U)` is the fibre product of
    `U ↪ X` along `π`, and `pullbackRestrictIsoRestrict` identifies the fibre product `π ×_X U`
    with the open subscheme `π⁻¹U`. -/

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.affineIso {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) :
    ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).toScheme ≅
      AlgebraicGeometry.Spec (CommRingCat.of (A.sectionsRing U.1)) :=
  (AlgebraicGeometry.pullbackRestrictIsoRestrict (AlgebraicGeometry.Scheme.relativeSpec A).hom U.1).symm ≪≫
    (A.toAffineAlgebra.chart_isPullback ⟨U.1, U.2⟩).flip.isoPullback.symm

/-- The inverse of `affineIso` followed by the open immersion `π⁻¹U ↪ Spec_X A` is the chart
    `AffineAlgebra.chart`. -/

theorem AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv ≫
        ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι =
      A.toAffineAlgebra.chart ⟨U.1, U.2⟩ := by
  exact (CategoryTheory.Category.assoc _ _ _).trans
    ((congrArg _ (AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_ι _ _)).trans
      (CategoryTheory.IsPullback.isoPullback_hom_fst _))

end
