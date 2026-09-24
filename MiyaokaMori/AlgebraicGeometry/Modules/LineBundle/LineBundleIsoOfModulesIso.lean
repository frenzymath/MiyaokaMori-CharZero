import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle

/-! # Isomorphisms of line bundles vs. isomorphisms of the underlying modules

The category structure of `LineBundle X` is induced by `toModules` (`InducedCategory`), so `L ≅ M` and
`L.toModules ≅ M.toModules` determine each other.
-/

set_option autoImplicit false

open CategoryTheory

noncomputable section

/-- An isomorphism of the underlying modules gives an isomorphism of line bundles. -/
def lineBundleIsoOfModulesIso {k : Type*} [Field k] {V : Variety k}
    {L M : LineBundle V} (e : L.toModules ≅ M.toModules) : L ≅ M :=
  { hom := CategoryTheory.InducedCategory.homMk e.hom
    inv := CategoryTheory.InducedCategory.homMk e.inv
    hom_inv_id := by
      apply CategoryTheory.InducedCategory.hom_ext
      exact e.hom_inv_id
    inv_hom_id := by
      apply CategoryTheory.InducedCategory.hom_ext
      exact e.inv_hom_id }

/-- An isomorphism of line bundles gives an isomorphism of the underlying modules. -/
def modulesIsoOfLineBundleIso {k : Type*} [Field k] {V : Variety k}
    {L M : LineBundle V} (e : L ≅ M) : L.toModules ≅ M.toModules :=
  { hom := e.hom.hom
    inv := e.inv.hom
    hom_inv_id := by
      have h := congrArg (fun q => q.hom) e.hom_inv_id
      change e.hom.hom ≫ e.inv.hom = 𝟙 L.toModules at h
      exact h
    inv_hom_id := by
      have h := congrArg (fun q => q.hom) e.inv_hom_id
      change e.inv.hom ≫ e.hom.hom = 𝟙 M.toModules at h
      exact h }

end
