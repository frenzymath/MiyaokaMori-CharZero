import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonIsoExt
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSheafificationUnit
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestrictionComparisonIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-!
# The exterior-dual comparison commutes with restriction to an open subscheme

For `U : X.Opens`, the restriction of `exteriorDualComparison M n` to `U` fits into a square
with `exteriorDualComparison (M.restrict U.ι) n`, the exterior-power restriction comparison
`moduleExteriorRestrictComparison` (an isomorphism, `ExteriorPowerRestrictionComparisonIso`) and the
dual restriction isomorphism `DualRestrict.dualRestrictIso`:

`a₁ ≫ (restrict ι).map (edc M n) ≫ d₂.hom = ⋀ⁿ(d.hom) ≫ edc (M|_U) n ≫ (a₂)^∨`

(`restrict_square`). Both sides are morphisms out of a sheafified exterior power into a dual
sheaf, so they are compared on wedge sections (`moduleExteriorPower_hom_ext`) and, as compatible
families of functionals on the restricted exterior power, on wedge sections again
(`localDual_ext_of_wedge`); there both sides are the same determinant of functional values
(`exteriorDualComparison_wedge_eval`). Consequently invertibility of the comparison of the
restricted module implies invertibility of the restricted comparison
(`exteriorDualComparison_restrict_isIso`).

Sources: Stacks Project, `modules.tex`, Internal Hom and Symmetric and exterior powers (both
compatible with restriction to opens by construction).

The invertibility of `moduleExteriorRestrictComparison U.ι M n` comes from
`ExteriorPowerRestrictionComparisonIso` (identification with the "sheafification commutes with
restriction" map).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false

open ModuleDualSheafificationUnit DualRestrict
open MiyaokaMori.ModuleDualSectionEquiv (unit_isIso unitIso unitIso_hom sectionEquiv sectionEquiv_apply
  sectionEquiv_restrict)

namespace ExteriorDualComparisonRestrict

variable {X : Scheme.{u}} (M : X.Modules) (n : ℕ) (U : X.Opens)

/-- Restricting a module morphism to an open subscheme acts on sections over `V` as the
original morphism over the image open. -/
theorem restrictFunctor_map_app {M N : X.Modules} (φ : M ⟶ N) (V : U.toScheme.Opens)
    (s : Γ(M.restrict U.ι, V)) :
    ((Scheme.Modules.restrictFunctor U.ι).map φ).app V s = φ.app (U.ι ''ᵁ V) s := rfl

/-- Precomposition with an isomorphism is injective on compatible families of functionals. -/
theorem localDualSectionsPrecomp_injective {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    Function.Injective (localDualSectionsPrecomp e.hom V) := by
  intro α β h
  have h' := congrArg (localDualSectionsPrecomp e.inv V) h
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← localDualSectionsPrecomp_comp, e.inv_hom_id, localDualSectionsPrecomp_id] at h'
  exact h'

/-- The restricted exterior power of `M` is the exterior power of the restriction: the wedge of
restricted sections goes to the wedge over the image open. -/
theorem restrictComparison_wedge (V : U.toScheme.Opens) (w : Fin n → Γ(M.restrict U.ι, V)) :
    (moduleExteriorRestrictComparison U.ι M n).app V
        (moduleExteriorWedge U.toScheme (M.restrict U.ι) n V w) =
      moduleExteriorWedge X M n (U.ι ''ᵁ V) w := by
  rw [moduleExteriorRestrictComparison_wedge]
  rfl

/-- The square relating the restricted comparison with the comparison of the restriction:
`a₁ ≫ (restrict ι).map (edc M n) ≫ d₂.hom ≫ (a₂)^∨ = ⋀ⁿ(d.hom) ≫ edc (M|_U) n`. -/
theorem restrict_square :
    moduleExteriorRestrictComparison U.ι (moduleSheafDual M) n ≫
        (Scheme.Modules.restrictFunctor U.ι).map (exteriorDualComparison M n) ≫
        (dualRestrictIso X U (moduleExteriorPower X M n)).hom ≫
        moduleSheafDualMap (moduleExteriorRestrictComparison U.ι M n) =
      (moduleExteriorIso U.toScheme n (dualRestrictIso X U M)).hom ≫
        exteriorDualComparison (M.restrict U.ι) n := by
  apply moduleExteriorPower_hom_ext
  intro V v
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, moduleExteriorIso_hom]
  rw [restrictComparison_wedge, moduleExteriorMap_wedge, restrictFunctor_map_app]
  apply (sectionEquiv (moduleExteriorPower U.toScheme (M.restrict U.ι) n) V).symm.injective
  apply localDual_ext_of_wedge
  intro W w
  rw [ExteriorDualComparisonNaturality.dualMap_eval, restrictComparison_wedge,
    dualRestrictIso_hom_app_val, exteriorDualComparison_wedge_eval]
  refine (exteriorDualComparison_wedge_eval M n (U.ι ''ᵁ V) v
    ((Over.post U.ι.opensFunctor).obj W) w).trans ?_
  congr 1
  ext i j
  exact (dualRestrictIso_hom_app_val X U M V (v j) W (w i)).symm

/-- Restricting the comparison to an open subscheme gives an invertible morphism as soon as
the comparison of the restricted module is invertible. -/
theorem restrict_isIso (h : IsIso (exteriorDualComparison (M.restrict U.ι) n)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (exteriorDualComparison M n)) := by
  have := h
  have := ExteriorPowerRestrictionComparison.moduleExteriorRestrictComparison_isIso (moduleSheafDual M) n U
  have := ExteriorPowerRestrictionComparison.moduleExteriorRestrictComparison_isIso M n U
  let D := moduleSheafDualIso (asIso (moduleExteriorRestrictComparison U.ι M n))
  have hD : moduleSheafDualMap (moduleExteriorRestrictComparison U.ι M n) = D.hom := rfl
  have key : (Scheme.Modules.restrictFunctor U.ι).map (exteriorDualComparison M n) =
      inv (moduleExteriorRestrictComparison U.ι (moduleSheafDual M) n) ≫
        ((moduleExteriorIso U.toScheme n (dualRestrictIso X U M)).hom ≫
          exteriorDualComparison (M.restrict U.ι) n) ≫
        D.inv ≫ (dualRestrictIso X U (moduleExteriorPower X M n)).inv := by
    rw [← restrict_square M n U, hD]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [key]
  infer_instance

end ExteriorDualComparisonRestrict

end AlgebraicGeometry.Scheme.Modules
