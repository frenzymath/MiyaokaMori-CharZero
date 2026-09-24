import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerPullbackStalkBijective
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso

/-!
# The canonical exterior-power pullback isomorphism

The actual pullback stalk tensor maps are bijective. Together with exterior-power
base change and the stalk conjugacy, this proves that the original exterior
pullback comparison is an isomorphism. The construction works for arbitrary
modules and all exterior degrees, including zero.

This supplies the comparison used for the determinant of a pullback. The stalk identification is
the one in Stacks Project, `sheaves.tex`, `lemma-stalk-pullback-modules`; the bijectivity of the stalk
tensor map is `MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective`
(`ModulePullbackStalkTensorBijective`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules
open MiyaokaMori.Algebra

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ)

/-- The original exterior pullback comparison is invertible for every module and degree. -/
theorem moduleExteriorPullbackComparison_isIso :
    IsIso (moduleExteriorPullbackComparison f M n) := by
  apply (moduleHom_isIso_iff_stalk_bijective
    (moduleExteriorPullbackComparison f M n)).mpr
  intro x
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    modulePullbackStalkAlgebra f x
  have hBase : Function.Bijective
      (exteriorPowerBaseChangeMap
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (M.presheaf.stalk (f x)) n) :=
    (exteriorPowerBaseChange
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (M.presheaf.stalk (f x)) n).bijective
  exact moduleExteriorPullbackComparison_stalk_bijective_of_bijective f M n x
    (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective f M x) hBase
    (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective f
      (moduleExteriorPower Y M n) x)

/-- Pullback commutes with exterior powers via the original canonical comparison. -/
def moduleExteriorPullbackIso :
    (Scheme.Modules.pullback f).obj (moduleExteriorPower Y M n) ≅
      moduleExteriorPower X ((Scheme.Modules.pullback f).obj M) n := by
  letI := moduleExteriorPullbackComparison_isIso f M n
  exact asIso (moduleExteriorPullbackComparison f M n)

/-- The forward morphism of the isomorphism is the original exterior pullback comparison. -/
@[simp]
theorem moduleExteriorPullbackIso_hom :
    (moduleExteriorPullbackIso f M n).hom = moduleExteriorPullbackComparison f M n := rfl

end AlgebraicGeometry.Scheme.Modules
