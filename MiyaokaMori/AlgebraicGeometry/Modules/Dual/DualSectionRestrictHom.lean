import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen

/-! # Sections of the dual sheaf as morphisms of the restriction

`Γ(M^∨, U) ≃ (M|_U ⟶ O_U)`: a section of the dual sheaf over `U` is an `O_U`-linear functional on `U`.

References: Stacks 01CM (sections of the internal Hom sheaf are morphisms between the restricted
sheaves); `moduleDualPresheaf` (`U ↦` compatible families of local functionals) and
`moduleDualPresheaf_isSheaf`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.DualSectionRestrictHom



variable {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules)

/-- An open `W ≤ ⊤` viewed as an object of `Over ⊤`. -/
abbrev overTop (W : Y.Opens) : Over (⊤ : Y.Opens) := Over.mk (homOfLE (le_top : W ≤ ⊤))

set_option backward.isDefEq.respectTransparency false in
/-- From a compatible family of local functionals (over `⊤`) to a morphism of sheaves of modules
`N ⟶ O_Y`: the component at `W` is `φ_{W ≤ ⊤}`; naturality is the restriction compatibility of `φ`. -/
def homOfTopFamily (φ : LocalDualSections Y N ⊤) : N ⟶ SheafOfModules.unit Y.ringCatSheaf where
  val :=
    { app := fun W => ModuleCat.ofHom
        { toFun := fun x => φ.1 (overTop W.unop) x
          map_add' := (φ.1 (overTop W.unop)).map_add
          map_smul' := (φ.1 (overTop W.unop)).map_smul }
      naturality := by
        intro W W' i
        ext x
        exact φ.2 (overTop W'.unop) (overTop W.unop)
          (@Over.homMk _ _ _ (overTop W'.unop) (overTop W.unop) i.unop (Subsingleton.elim _ _)) x }

set_option backward.isDefEq.respectTransparency false in
/-- From a morphism of sheaves of modules `N ⟶ O_Y` to a compatible family of local functionals
(over `⊤`): take the components; compatibility is `naturality_apply`. -/
def topFamilyOfHom (ψ : N ⟶ SheafOfModules.unit Y.ringCatSheaf) : LocalDualSections Y N ⊤ :=
  ⟨fun V ↦ (ψ.val.app (op V.left)).hom,
    fun _ _ j s ↦ PresheafOfModules.naturality_apply ψ.val j.left.op s⟩

set_option backward.isDefEq.respectTransparency false in
/-- The case `U = ⊤`: compatible families of local functionals `≃` morphisms `N ⟶ O_Y` (both
directions take the same component). -/
def topFamilyEquivHom : LocalDualSections Y N ⊤ ≃ (N ⟶ SheafOfModules.unit Y.ringCatSheaf) where
  toFun := homOfTopFamily N
  invFun := topFamilyOfHom N
  left_inv φ := by
    apply Subtype.ext
    funext V
    rcases V with ⟨L, ⟨⟨⟩⟩, h⟩
    rfl
  right_inv ψ := rfl

end AlgebraicGeometry.Scheme.Modules.DualSectionRestrictHom

/-- Compatible families of local functionals over `U` are the morphisms `M|_U ⟶ O_U` on `U`.

Proof (both directions are repackagings open by open, with no geometric content):
(1) `Equiv.cast`: `U.ι ''ᵁ ⊤ = U` (`Scheme.Opens.ι_image_top`), so
`LocalDualSections X M U = LocalDualSections X M (U.ι ''ᵁ ⊤)`.
(2) `openLocalDualRestrictLinearEquiv X U M ⊤` (`DualRestrictOpen`): compatible families on `X` inside
`U.ι ''ᵁ ⊤` `≃` compatible families on `U` inside `⊤` for `M.restrict U.ι` (using
`Γ(M.restrict U.ι, W) = Γ(M, U.ι ''ᵁ W)` and `Γ(U, W) = Γ(X, U.ι ''ᵁ W)`, both `rfl`:
`Scheme.Modules.restrict_obj`, `Scheme.Opens.toScheme_presheaf_obj`; the scalar actions match through
`Scheme.Opens.ι_appIso`).
(3) `topFamilyEquivHom` (this file): on any scheme `Y`, `LocalDualSections Y N ⊤ ≃ (N ⟶ O_Y)`, with
components `W ↦ φ_{W ≤ ⊤}`; naturality is restriction compatibility, and the two directions are
inverse by `rfl`.
Edge cases: for `U = ⊥` both sides have only the zero element; for `M = 0` both sides are zero. -/
theorem AlgebraicGeometry.Scheme.Modules.nonempty_localDualSections_equiv_restrictHom
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.LocalDualSections X M U ≃
      (M.restrict U.ι ⟶ SheafOfModules.unit U.toScheme.ringCatSheaf)) :=
  ⟨(Equiv.cast (congrArg (fun V : X.Opens => (AlgebraicGeometry.Scheme.Modules.LocalDualSections X M V : Type u))
      U.ι_image_top.symm)).trans
    ((MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M ⊤).toEquiv.trans
      (AlgebraicGeometry.Scheme.Modules.DualSectionRestrictHom.topFamilyEquivHom (M.restrict U.ι)))⟩

/-- `Γ(M^∨, U) ≃ (M|_U ⟶ O_U)`: `ModuleDualSectionEquiv.sectionEquiv` composed with the previous
lemma.

With it, the argument `α` of `totalSpace.coordinateFunctionOn` can be built from a frame `a` of a line
bundle: `α := (this equivalence).symm (the hom of Scheme.Modules.IsFrame.restrictIso)`. -/
theorem AlgebraicGeometry.Scheme.Modules.nonempty_dualSections_equiv_restrictHom
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Nonempty (Γ(AlgebraicGeometry.Scheme.Modules.dual M, U) ≃
      (M.restrict U.ι ⟶ SheafOfModules.unit U.toScheme.ringCatSheaf)) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_localDualSections_equiv_restrictHom M U
  exact ⟨(MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).toEquiv.symm.trans e⟩

end
