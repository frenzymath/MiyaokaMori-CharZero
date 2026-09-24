import MiyaokaMori.Prelude
import Mathlib.CategoryTheory.Sites.LocallyInjective
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection

/-! # The morphism attached to a regular section is a monomorphism

Monomorphisms of `O_X`-modules are detected on sections, and the morphism `σ_s : O_X → M`
attached to a global section `s` of `M` (`homOfTopSection`) is `r ↦ r • s|_U` on sections; hence
`σ_s` is a monomorphism as soon as `s` is regular (`r • s|_U = 0 ⇒ r = 0` on every open `U`).

* `mono_of_injective_app` (Stacks 00WN / Mathlib `Sheaf.mono_of_isLocallyInjective`): the forgetful
  functor to sheaves of abelian groups is faithful, hence reflects monomorphisms; a morphism of sheaves
  which is injective on every open is locally injective, hence a monomorphism of sheaves.
* `homOfTopSection_app`: `(homOfTopSection M s).app U r = r • s|_U`
  (`unitHomEquiv_apply_coe` gives the value at `1`; linearity gives the value at `r`).
* `mono_homOfTopSection_of_injective`: combination of the two.

Used for the left end of the section restriction sequence `0 → N → L → i_*i^*L → 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A morphism of `O_X`-modules injective on all sections is a monomorphism. -/
theorem mono_of_injective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.Opens, Function.Injective (φ.app U)) : Mono φ := by
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun U => h U.unop)
  have : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    Sheaf.mono_of_isLocallyInjective _
  exact (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map this

/-- `homOfTopSection M s` sends `1 ∈ Γ(X, U)` to `s|_U`. -/
theorem homOfTopSection_val_app_one (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.homOfTopSection M s).val.app (op U) (1 : Γ(X, U)) =
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s := by
  have h := SheafOfModules.unitHomEquiv_apply_coe M
    (AlgebraicGeometry.Scheme.Modules.homOfTopSection M s) (op U)
  refine h.symm.trans ?_
  exact congrArg (fun z : M.sections => z.val (op U))
    ((SheafOfModules.unitHomEquiv M).apply_symm_apply _)

/-- `homOfTopSection M s` is `r ↦ r • s|_U` on sections over `U`. -/
theorem homOfTopSection_val_app (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U)) :
    (AlgebraicGeometry.Scheme.Modules.homOfTopSection M s).val.app (op U) r =
      r • (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s := by
  rw [← homOfTopSection_val_app_one]
  have := ((AlgebraicGeometry.Scheme.Modules.homOfTopSection M s).val.app (op U)).hom.map_smul r
    (1 : Γ(X, U))
  refine Eq.trans ?_ this
  congr 1
  exact (mul_one r).symm

/-- `σ_s : O_X → M` is a monomorphism when `s` is regular. -/
theorem mono_homOfTopSection_of_injective (M : X.Modules) (s : Γ(M, ⊤))
    (hs : ∀ U : X.Opens, Function.Injective (fun r : Γ(X, U) =>
      r • ((M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s : Γ(M, U)))) :
    Mono (AlgebraicGeometry.Scheme.Modules.homOfTopSection M s) := by
  refine mono_of_injective_app _ fun U r r' h => hs U ?_
  exact (homOfTopSection_val_app M s U r).symm.trans
    (h.trans (homOfTopSection_val_app M s U r'))

end AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux

end
