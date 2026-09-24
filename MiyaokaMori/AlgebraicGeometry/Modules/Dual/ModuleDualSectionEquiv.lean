import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualPresheafSheaf

/-! # Sections of the dual sheaf and compatible families of local functionals

Let `M` be an `O_X`-module on a scheme `X`. The presheaf `moduleDualPresheaf M`
(`U ↦ Hom_{O_U}(M|_U, O_U)`) of compatible families of local functionals is already a sheaf, so the
sheafification unit `moduleDualPresheaf M → (underlying presheaf of M^∨)` is an isomorphism;
evaluating on each open `U` gives a `Γ(X,U)`-linear isomorphism
`sectionEquiv M U : LocalDualSections X M U ≃ Γ(M^∨, U)`, whose forward direction is the component of
the sheafification unit, compatible with restriction. No local freeness is needed.

Proof sketch:
1. `moduleDualPresheaf_isSheaf`: the underlying presheaf of abelian groups of `moduleDualPresheaf M`
   is a sheaf.
2. `PresheafOfModules.toPresheaf` reflects isomorphisms;
   `toPresheaf_map_sheafificationAdjunction_unit_app` identifies the underlying map of the
   sheafification unit with `toSheafify`, and `CategoryTheory.isIso_toSheafify` gives the isomorphism.
3. Apply the evaluation functor at `U` to the isomorphism to get the linear isomorphism; compatibility
   with restriction is the naturality of the unit (`PresheafOfModules.naturality_apply`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace MiyaokaMori.ModuleDualSectionEquiv

open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (M : X.Modules)

/-- The dual presheaf is already a sheaf, so the sheafification unit is invertible. -/
theorem unit_isIso :
    IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (moduleDualPresheaf M)) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)]
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact CategoryTheory.isIso_toSheafify (Opens.grothendieckTopology X)
    (ModuleDualPresheafSheaf.moduleDualPresheaf_isSheaf M)

/-- The isomorphism whose forward direction is the sheafification unit. -/
def unitIso :
    moduleDualPresheaf M ≅
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        ((Scheme.Modules.toPresheafOfModules X).obj (moduleSheafDual M)) := by
  letI := unit_isIso M
  exact asIso ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (moduleDualPresheaf M))

@[simp]
theorem unitIso_hom :
    (unitIso M).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (moduleDualPresheaf M) := rfl

/-- The linear isomorphism between compatible families of local functionals and sections of the dual
sheaf. -/
def sectionEquiv (U : X.Opens) :
    LocalDualSections X M U ≃ₗ[Γ(X, U)] Γ(moduleSheafDual M, U) :=
  ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)).mapIso
    (unitIso M)).toLinearEquiv

@[simp]
theorem sectionEquiv_apply (U : X.Opens) (φ : LocalDualSections X M U) :
    sectionEquiv M U φ =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (moduleDualPresheaf M)).app (op U)) φ := rfl

/-- Compatibility with restriction. -/
theorem sectionEquiv_restrict {U V : X.Opens} (i : V ⟶ U)
    (φ : LocalDualSections X M U) :
    (moduleSheafDual M).presheaf.map i.op (sectionEquiv M U φ) =
      sectionEquiv M V (localDualRestrict M i φ) := by
  exact (PresheafOfModules.naturality_apply (unitIso M).hom i.op φ).symm

end MiyaokaMori.ModuleDualSectionEquiv
