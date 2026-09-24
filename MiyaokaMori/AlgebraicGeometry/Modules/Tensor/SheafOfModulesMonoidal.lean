import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.CategoryTheory.SiteModulesMonoidal

/-! # The symmetric monoidal structure on sheaves of modules over a scheme

Sheafifying the symmetric monoidal structure on presheaves of modules gives a symmetric monoidal
structure on sheaves of modules, in particular on `X.Modules`.

The construction itself lives in `SiteModulesMonoidal` (an arbitrary site and a `CommRingCat`-valued
sheaf of rings); this file only specializes it to schemes. `ringCatSheafOfComm X.sheaf` and
`X.ringCatSheaf` are `rfl`, so `SheafOfModules X.ringCatSheaf` (e.g. `M.over U` on the slice site
`J.over U`) and `X.Modules` use the **same** monoidal structure term, not two definitionally equal
but syntactically different ones.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The sheafification of the unit presheaf of modules (the structure presheaf) is the structure
sheaf. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso (X : AlgebraicGeometry.Scheme.{u}) :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorUnit (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  SiteModules.sheafificationUnitIso X.sheaf

/-- The monoidal structure on `X.Modules`, obtained by sheafifying the one on presheaves of modules. -/
noncomputable instance AlgebraicGeometry.Scheme.Modules.monoidalCategory (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.MonoidalCategory X.Modules :=
  SiteModules.monoidalCategory X.sheaf

/-- The symmetric structure on `X.Modules`. -/
noncomputable instance AlgebraicGeometry.Scheme.Modules.symmetricCategory (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.SymmetricCategory X.Modules :=
  SiteModules.symmetricCategory X.sheaf

end
