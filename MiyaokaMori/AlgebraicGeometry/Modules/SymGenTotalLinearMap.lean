import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalProjection

/-! # The degree-one inclusion of the symmetric algebra as a linear map

The degree-one inclusion of the sheaf symmetric algebra on sections, as a linear map:
for `W : X.Modules` and an open `U`, `ι_U : Γ(U, W) → A(U) := Γ(U, Sym W) = (symGradedAlgebra W).total.sectionsRing U`
is `symGen W ≫ totalIncl 1` on sections (`WeightedSymGenerator.symGen`, `GradedAlgebraTotalProjection.totalIncl`),
packaged as a `Γ(X, U)`-linear map `symGenTotalLinearMap W U`, where `A(U)` is a `Γ(X, U)`-algebra through
`sectionsUnit` (`r • a = sectionsUnit r * a`, `QCAlgebra.smul_eq_sectionsUnit_mul`).

This is the map `ι_U` of `IsSymmetricAlgebra ι_U` (`SymGradedAlgebraSectionsIsSymmetricAlgebra`), of the
surjectivity/retraction lemmas for the sections of the total space
(`TotalSpaceSectionsRingEquivMvPolynomialSymSections*`) and of `totalSpace.linearFunctionLinearMap`
(`OmegaTotalSpaceIsoPullbackDual`).

Definition only (no proof obligations beyond linearity). References: Bourbaki Algebra III §6 no. 1 (the
canonical map `M → Sym M`); Stacks 01CG. Kept in its own module so that the modules proving the two halves
of `IsSymmetricAlgebra ι_U` and the module stating it can all import the definition without an import cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree-one inclusion `Γ(U, W) → A(U) = Γ(U, Sym(W))` (`symGen W ≫ totalIncl 1` on sections) as a
`Γ(X, U)`-linear map, `A(U)` being a `Γ(X, U)`-algebra through `sectionsUnit`
(`r • a = sectionsUnit r * a`, `QCAlgebra.smul_eq_sectionsUnit_mul`). -/
def AlgebraicGeometry.Scheme.Modules.symGenTotalLinearMap {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) (U : X.Opens) :
    letI := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.sectionsUnit U).toAlgebra
    Γ(W, U) →ₗ[Γ(X, U)] (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.sectionsRing U :=
  letI := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.sectionsUnit U).toAlgebra
  { toFun := fun ξ => (AlgebraicGeometry.Scheme.Modules.symGen W ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).totalIncl 1).app U ξ
    map_add' := fun a b => map_add ((AlgebraicGeometry.Scheme.Modules.symGen W ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).totalIncl 1).app U).hom a b
    map_smul' := fun r a => by
      rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
      exact (AlgebraicGeometry.Scheme.QCAlgebra.smul_eq_sectionsUnit_mul _ U r _).symm }

theorem AlgebraicGeometry.Scheme.Modules.symGenTotalLinearMap_apply {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) (U : X.Opens) (ξ : Γ(W, U)) :
    letI := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.sectionsUnit U).toAlgebra
    AlgebraicGeometry.Scheme.Modules.symGenTotalLinearMap W U ξ =
      (AlgebraicGeometry.Scheme.Modules.symGen W ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).totalIncl 1).app U ξ := rfl

end
