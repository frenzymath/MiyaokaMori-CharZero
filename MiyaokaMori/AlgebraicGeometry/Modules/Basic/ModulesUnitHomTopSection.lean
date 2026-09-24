import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Global sections and morphisms from the structure sheaf

Global sections of a sheaf of modules correspond to morphisms from the structure sheaf:
`s ∈ Γ(X, M) ↦ (O_X → M, 1 ↦ s)`, `σ ↦ σ(1)`; `Hom(O_X, M) ≃ Γ(X, M)`. (Used to describe `T`-points of
`Tot(V)` as sections of `g^*V`.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- A global section `s ∈ Γ(X, M)` ↦ the morphism `O_X → M` (`1 ↦ s`): Mathlib's `SheafOfModules.unitHomEquiv`
   (`Hom(O, M) ≃` compatible families of sections of `M`), the compatible family being the restrictions of `s`
   to the opens; compatibility (presheaf functoriality) is a proof obligation. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.homOfTopSection {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm
    (_root_.PresheafOfModules.sectionsMk
      (fun U => (M.val.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom s)
      (fun U W f => by
        have h : M.val.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op ≫ M.val.presheaf.map f =
            M.val.presheaf.map (CategoryTheory.homOfLE (le_top : W.unop ≤ ⊤)).op := by
          rw [← M.val.presheaf.map_comp]; rfl
        exact congrArg (fun φ => φ.hom s) h))

/- The other direction: a morphism `σ : O_X → M` ↦ `σ(1) ∈ Γ(X, M)`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.topSectionOfHom {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (σ : SheafOfModules.unit X.ringCatSheaf ⟶ M) : (M.val.obj (Opposite.op ⊤) : Type u) :=
  (σ.val.app (Opposite.op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))

/- `Hom(O_X, M) ≃ Γ(X, M)`; the inverse laws are proof obligations (sections of a sheaf are determined by
   restrictions of global sections: `⊤` is the terminal object of `X.Opens`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.unitHomEquivTop {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ M) ≃ (M.val.obj (Opposite.op ⊤) : Type u) where
  toFun := AlgebraicGeometry.Scheme.Modules.topSectionOfHom M
  invFun := AlgebraicGeometry.Scheme.Modules.homOfTopSection M
  left_inv := fun σ => by
    -- both sides are morphisms `unit ⟶ M`; by injectivity of `unitHomEquiv` reduce to equality of the
    -- compatible families of sections, which on each open says "restriction of the global section = σ
    -- applied to 1 on that open", i.e. the compatibility of `unitHomEquiv M σ` as a family of sections
    refine (Equiv.symm_apply_eq _).2 ?_
    ext U
    exact _root_.PresheafOfModules.sections_property (SheafOfModules.unitHomEquiv M σ)
      (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op
  right_inv := fun s => by
    -- the value of σ(1) at ⊤ is the value of the family at ⊤, and the restriction map of ⊤ ≤ ⊤ is the identity
    show ((SheafOfModules.unitHomEquiv M)
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection M s)).val (Opposite.op ⊤) = s
    simp only [AlgebraicGeometry.Scheme.Modules.homOfTopSection, Equiv.apply_symm_apply]
    show (M.val.presheaf.map
      (CategoryTheory.homOfLE (le_top : (Opposite.op (⊤ : X.Opens)).unop ≤ ⊤)).op).hom s = s
    rw [show (CategoryTheory.homOfLE (le_top : (Opposite.op (⊤ : X.Opens)).unop ≤ ⊤)).op
        = 𝟙 (Opposite.op (⊤ : X.Opens)) from rfl, M.val.presheaf.map_id]
    rfl

end
