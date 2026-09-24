import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv
import Mathlib.Topology.Sheaves.Stalks

/-!
# The dual sheafification unit and its sections: inverse, restriction and germ formulas

The compatible local functionals already form a sheaf, so the module sheafification unit of the
dual presheaf is an isomorphism and evaluating it gives the linear equivalence
`sectionEquiv M U : LocalDualSections X M U ≃ₗ[Γ(X, U)] Γ(moduleSheafDual M, U)` with sections of the
canonical `moduleSheafDual`. That equivalence is `MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv`
(`ModuleDualSectionEquiv`, together with `unit_isIso`, `unitIso`, `unitIso_hom`, `sectionEquiv_apply`,
`sectionEquiv_restrict`). This file contains the further lemmas about it: the inverse formulas,
restriction of the inverse, and the germ formula.

Sources: Stacks Project, `modules.tex`, section `Internal Hom`; the sheafification adjunction for
modules. This supplies the local-functional interface for the dual and determinant comparison.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.ModuleDualSheafificationUnit

open MiyaokaMori.ModuleDualSectionEquiv

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (M : X.Modules)

/-- The inverse section map is the component of the inverse of the original unit. -/
theorem sectionEquiv_symm_apply (U : X.Opens) (s : Γ(moduleSheafDual M, U)) :
    (sectionEquiv M U).symm s = (unitIso M).inv.app (op U) s := rfl

/-- Passing to the dual sheaf and back recovers the original compatible functional. -/
theorem sectionEquiv_symm_apply_apply (U : X.Opens) (φ : LocalDualSections X M U) :
    (sectionEquiv M U).symm (sectionEquiv M U φ) = φ :=
  (sectionEquiv M U).symm_apply_apply φ

/-- Every dual-sheaf section is recovered after applying the inverse and the unit. -/
theorem sectionEquiv_apply_symm_apply (U : X.Opens) (s : Γ(moduleSheafDual M, U)) :
    sectionEquiv M U ((sectionEquiv M U).symm s) = s :=
  (sectionEquiv M U).apply_symm_apply s

/-- The inverse equivalence also respects restriction to smaller opens. -/
theorem sectionEquiv_symm_restrict {U V : X.Opens} (i : V ⟶ U)
    (s : Γ(moduleSheafDual M, U)) :
    (sectionEquiv M V).symm ((moduleSheafDual M).presheaf.map i.op s) =
      localDualRestrict M i ((sectionEquiv M U).symm s) := by
  apply (sectionEquiv M V).injective
  rw [LinearEquiv.apply_symm_apply, ← sectionEquiv_restrict,
    LinearEquiv.apply_symm_apply]

/-- A section's image has exactly the germ obtained by the original unit's stalk map. -/
theorem germ_sectionEquiv (U : X.Opens) (x : X) (hx : x ∈ U)
    (φ : LocalDualSections X M U) :
    (moduleSheafDual M).presheaf.germ U x hx (sectionEquiv M U φ) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (moduleDualPresheaf M)))
        (TopCat.Presheaf.germ (moduleDualPresheaf M).presheaf U x hx φ) := by
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app (moduleDualPresheaf M))) φ).symm

end AlgebraicGeometry.Scheme.Modules.ModuleDualSheafificationUnit
