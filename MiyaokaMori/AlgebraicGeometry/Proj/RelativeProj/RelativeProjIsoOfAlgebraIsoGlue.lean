import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIsoChart
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # Isomorphic graded algebras have isomorphic relative Proj, step 3: gluing the chart isomorphisms

The chart isomorphisms `chartIso φ U : Proj A_S(U) ≅ Proj A_T(U)` (step 2) form a natural
isomorphism `natIso φ : S.projFunctor ≅ T.projFunctor` of the gluing functors on the small affine
Zariski site; taking colimits (`HasColimit.isoOfNatIso`) gives the isomorphism of the glued schemes
`leftIso φ : Proj_X S ≅ Proj_X T`. It is compatible with the charts (`projChart_leftIso_hom`, from
`HasColimit.isoOfNatIso_ι_hom`) and with the structure morphisms to `X` (`leftIso_hom_comp`:
`colimit.hom_ext` reduces it to the chart-level statement `chartIso_hom_projToOpen`, using
`projChart_hom : projChart U ≫ π = projToOpen U ≫ ι_U`).

Source: Stacks 01NP; the same final step as for the Veronese isomorphism
(`relativeProj.veroneseIso.leftIso`, `ProjVeroneseIso.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The gluing functor `U ↦ Proj A(U)` has a colimit (it is `projGluingData.functor`, which is
locally directed). Registered only as a **local** instance: instance search does not unfold
`projGluingData` to see this. -/
theorem AlgebraicGeometry.Scheme.GradedAffineAlgebra.hasColimit_projFunctor
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedAffineAlgebra) :
    CategoryTheory.Limits.HasColimit S.projFunctor :=
  inferInstanceAs (CategoryTheory.Limits.HasColimit S.projGluingData.functor)

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso

attribute [local instance] AlgebraicGeometry.Scheme.GradedAffineAlgebra.hasColimit_projFunctor

variable {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ≅ T)

/-- The natural isomorphism of gluing functors `U ↦ Proj A_S(U)` and `U ↦ Proj A_T(U)`. -/
def natIso : S.toGradedAffineAlgebra.projFunctor ≅ T.toGradedAffineAlgebra.projFunctor :=
  CategoryTheory.NatIso.ofComponents (fun U => chartIso φ U) (fun f => chartIso_naturality φ f)

theorem natIso_hom_app (U : X.AffineZariskiSite) : (natIso φ).hom.app U = (chartIso φ U).hom := rfl

/-- The isomorphism of the glued schemes `Proj_X S ≅ Proj_X T`. -/
def leftIso : S.toGradedAffineAlgebra.relativeProj.left ≅ T.toGradedAffineAlgebra.relativeProj.left :=
  CategoryTheory.Limits.HasColimit.isoOfNatIso (natIso φ)

/-- The same isomorphism, typed through the name `Scheme.relativeProj` (an `abbrev` of
`GradedAffineAlgebra.relativeProj`, so the two types are reducibly defeq). -/
theorem leftIso_eq :
    (leftIso φ : (AlgebraicGeometry.Scheme.relativeProj S).left ≅
      (AlgebraicGeometry.Scheme.relativeProj T).left) =
    CategoryTheory.Limits.HasColimit.isoOfNatIso (natIso φ) := rfl

/-- Compatibility with the charts: `ι_U^S ≫ e = chartIso U ≫ ι_U^T`. -/
@[reassoc]
theorem projChart_leftIso_hom (U : X.AffineZariskiSite) :
    S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom =
      (chartIso φ U).hom ≫ T.toGradedAffineAlgebra.projChart U :=
  CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom (natIso φ) U

/-- Compatibility with the charts, inverse direction: `ι_U^T ≫ e⁻¹ = (chartIso U)⁻¹ ≫ ι_U^S`. -/
@[reassoc]
theorem projChart_leftIso_inv (U : X.AffineZariskiSite) :
    T.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).inv =
      (chartIso φ U).inv ≫ S.toGradedAffineAlgebra.projChart U :=
  CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_inv (natIso φ) U

/-- `e` is an isomorphism over `X`: `e ≫ π_T = π_S`. -/
theorem leftIso_hom_comp :
    (leftIso φ).hom ≫ T.toGradedAffineAlgebra.relativeProj.hom =
      S.toGradedAffineAlgebra.relativeProj.hom := by
  refine CategoryTheory.Limits.colimit.hom_ext fun U => ?_
  have hS := S.toGradedAffineAlgebra.projChart_hom U
  have hT := T.toGradedAffineAlgebra.projChart_hom U
  have hι := projChart_leftIso_hom φ U
  change S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom ≫
      T.toGradedAffineAlgebra.relativeProj.hom =
    S.toGradedAffineAlgebra.projChart U ≫ S.toGradedAffineAlgebra.relativeProj.hom
  rw [← Category.assoc, hι, Category.assoc, hT, hS, ← Category.assoc, chartIso_hom_projToOpen]

/-- `leftIso_hom_comp` through the old name `Scheme.relativeProj`. -/
theorem leftIso_hom_comp' :
    (leftIso φ).hom ≫ (AlgebraicGeometry.Scheme.relativeProj T).hom =
      (AlgebraicGeometry.Scheme.relativeProj S).hom :=
  leftIso_hom_comp φ

end AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso

end
