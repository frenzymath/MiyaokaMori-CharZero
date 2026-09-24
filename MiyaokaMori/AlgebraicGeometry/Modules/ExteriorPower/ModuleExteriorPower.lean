import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Exterior powers of module sheaves

For a module sheaf on a scheme, this file constructs the exterior-power presheaf
objectwise and then sheafifies it.  Restriction maps are induced by the alternating
universal property, so the construction uses the actual module sections on each open
and their restriction maps.  No rank or freeness hypothesis is built into the
construction.

This is the B0b source interface extracted from the rejected degree-comparison draft.
The same declarations are consumed by the tangent/determinant and pullback slices.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) (M : X.PresheafOfModules) (n : ℕ)

/- The sections of the structure sheaf on an open form the coefficient ring for the
   corresponding module object. -/
local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

set_option backward.isDefEq.respectTransparency false in
/-- The alternating map on wedge generators induced by a presheaf restriction. -/
def exteriorRestrictionAlternating {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (M.obj U).AlternatingMap
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
        ((M.obj V).exteriorPower n)) n where
  toFun v := exteriorPower.ιMulti Γ(X, V.unop) n (M.map i ∘ v)
  map_update_add' v j a b := by
    simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
  map_update_smul' v j r a := by
    simp only [Function.comp_update, M.map_smul, AlternatingMap.map_update_smul]
    rfl
  map_eq_zero_of_eq' v j l h hjl :=
    (exteriorPower.ιMulti Γ(X, V.unop) n).map_eq_zero_of_eq _
      (congrArg (M.map i) h) hjl

/-- Restriction on exterior powers, determined by restriction of wedge generators. -/
def exteriorRestriction {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (M.obj U).exteriorPower n ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
        ((M.obj V).exteriorPower n) :=
  ModuleCat.exteriorPower.desc (exteriorRestrictionAlternating X M n i)

/-- Restriction sends a wedge generator to the wedge of the restricted sections. -/
@[simp]
theorem exteriorRestriction_mk {U V : X.Opensᵒᵖ} (i : U ⟶ V) (v : Fin n → M.obj U) :
    exteriorRestriction X M n i (ModuleCat.exteriorPower.mk v) =
      ModuleCat.exteriorPower.mk (M := M.obj V) (M.map i ∘ v) :=
  ModuleCat.exteriorPower.desc_mk _ _

set_option backward.isDefEq.respectTransparency false in
/-- The exterior-power presheaf of a module presheaf on a scheme. -/
def moduleExteriorPresheaf : X.PresheafOfModules where
  obj U := (M.obj U).exteriorPower n
  map i := exteriorRestriction X M n i
  map_id U := by
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    simp only [ModuleCat.AlternatingMap.postcomp_apply, exteriorRestriction_mk]
    change ModuleCat.exteriorPower.mk (M := M.obj U) (M.map (𝟙 U) ∘ v) =
      ModuleCat.exteriorPower.mk (M := M.obj U) v
    congr 1
    funext j
    simp
  map_comp i j := by
    rename_i U V W
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    simp only [ModuleCat.AlternatingMap.postcomp_apply, exteriorRestriction_mk]
    change ModuleCat.exteriorPower.mk (M := M.obj W) (M.map (i ≫ j) ∘ v) =
      exteriorRestriction X M n j (exteriorRestriction X M n i
        (ModuleCat.exteriorPower.mk v))
    rw [exteriorRestriction_mk, exteriorRestriction_mk]
    congr 1
    funext l
    exact M.map_comp_apply i j (v l)

/-- Sheafification of the canonical exterior-power presheaf. -/
def moduleExteriorPower (F : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (moduleExteriorPresheaf X F.val n)

end AlgebraicGeometry.Scheme.Modules
