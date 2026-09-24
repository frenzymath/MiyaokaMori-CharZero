import MiyaokaMori.Prelude

/-! # Sheafification of a presheaf of modules whose underlying presheaf is a sheaf

Statement: `X` a scheme, `P` a presheaf of `O_X`-modules whose underlying presheaf of abelian groups is
already a sheaf. Then the module sheafification unit `P → (underlying presheaf of the sheafification of P)`
is an isomorphism; evaluating on each open `U` gives a `Γ(X,U)`-linear isomorphism
`sectionEquiv P hP U : P(U) ≃ Γ(P^sh, U)`, whose forward map is the component of the sheafification unit
and which commutes with restriction.

Proof:
1. `PresheafOfModules.toPresheaf` reflects isomorphisms, `toPresheaf_map_sheafificationAdjunction_unit_app`
   identifies the underlying map of the module sheafification unit with `toSheafify`, and
   `CategoryTheory.isIso_toSheafify` gives the isomorphism.
2. Apply the evaluation functor at `U` to the isomorphism to get the linear isomorphism; commuting with
   restriction is the naturality of the unit (`PresheafOfModules.naturality_apply`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace MiyaokaMori.PresheafOfModulesSheafSections

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (P : X.PresheafOfModules)
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P.presheaf)

/-- The module sheafification of `P`. -/
abbrev sheafify : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P

include hP in
/-- The underlying presheaf is already a sheaf, so the module sheafification unit is invertible. -/
theorem unit_isIso :
    IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)]
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact CategoryTheory.isIso_toSheafify (Opens.grothendieckTopology X) hP

/-- The isomorphism whose forward map is the sheafification unit. -/
def unitIso :
    P ≅ (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        ((Scheme.Modules.toPresheafOfModules X).obj (sheafify P)) := by
  letI := unit_isIso P hP
  exact asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)

/-- The linear isomorphism between presheaf sections and sheafified sections. -/
def sectionEquiv (U : X.Opens) : P.obj (op U) ≃ₗ[Γ(X, U)] Γ(sheafify P, U) :=
  ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)).mapIso (unitIso P hP)).toLinearEquiv

/-- Compatibility with restriction. -/
theorem sectionEquiv_restrict {U V : X.Opens} (i : V ⟶ U) (φ : P.obj (op U)) :
    (sheafify P).presheaf.map i.op (sectionEquiv P hP U φ) =
      sectionEquiv P hP V (P.map i.op φ) :=
  (PresheafOfModules.naturality_apply (unitIso P hP).hom i.op φ).symm

end MiyaokaMori.PresheafOfModulesSheafSections
