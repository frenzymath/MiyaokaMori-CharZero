import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle

/-! # Bundled line bundles

**Bundled line bundles** `X.LineBundle` on an arbitrary scheme `X`: a module `toModules` together with an
instance `toModules.IsLineBundle`. The category structure is that of the full subcategory of `X.Modules`
(the hom sets are by definition those of the underlying modules); `LineBundle.ofModules M` (with
`toModules` returning `M` by `rfl`), the structure sheaf `1`, pullback `L.pullback f` along any morphism,
and lifting of isomorphisms `LineBundle.isoMk`.

Design: the unbundled class `[M.IsLineBundle]` is primary and the bundled version is a thin wrapper around
it — one data field plus one `Prop` instance field, so the constructor has no proof obligations; local
freeness, finite type and rank `1` are theorems/instances about `IsLineBundle`, available automatically
through `L.toModules`. For "line bundles on a variety" write `X.toScheme.LineBundle`.

Reference: Stacks 01CR.
-/

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A bundled line bundle: a module together with "is a line bundle". -/
structure LineBundle (X : Scheme.{u}) where
  /-- the underlying module -/
  toModules : X.Modules
  [isLineBundle : toModules.IsLineBundle]

attribute [instance] LineBundle.isLineBundle

namespace LineBundle

variable {X Y : Scheme.{u}}

instance : CoeOut X.LineBundle X.Modules := ⟨toModules⟩

@[ext] theorem ext {L L' : X.LineBundle} (h : L.toModules = L'.toModules) : L = L' := by
  cases L; cases L'; cases h; rfl

/-- Morphisms = morphisms of the underlying modules. -/
instance : Category.{u} X.LineBundle where
  Hom L L' := L.toModules ⟶ L'.toModules
  id L := 𝟙 L.toModules
  comp {L₁ L₂ L₃} f g := CategoryStruct.comp (obj := X.Modules) (X := L₁.toModules)
    (Y := L₂.toModules) (Z := L₃.toModules) f g
  id_comp {L₁ L₂} f := Category.id_comp (obj := X.Modules) (X := L₁.toModules) (Y := L₂.toModules) f
  comp_id {L₁ L₂} f := Category.comp_id (obj := X.Modules) (X := L₁.toModules) (Y := L₂.toModules) f
  assoc {L₁ L₂ L₃ L₄} f g h := Category.assoc (obj := X.Modules) (W := L₁.toModules)
    (X := L₂.toModules) (Y := L₃.toModules) (Z := L₄.toModules) f g h

/-- The forgetful functor `X.LineBundle ⥤ X.Modules` (fully faithful: the hom sets are the same by definition). -/
def forget (X : Scheme.{u}) : X.LineBundle ⥤ X.Modules where
  obj := toModules
  map f := f

@[simp] theorem forget_obj (L : X.LineBundle) : (forget X).obj L = L.toModules := rfl

/-- Unbundled → bundled. -/
def ofModules (M : X.Modules) [M.IsLineBundle] : X.LineBundle := ⟨M⟩

@[simp] theorem toModules_ofModules (M : X.Modules) [M.IsLineBundle] : (ofModules M).toModules = M := rfl

@[simp] theorem ofModules_toModules (L : X.LineBundle) : ofModules L.toModules = L := rfl

/-- An isomorphism of the underlying modules lifts to an isomorphism of line bundles. -/
def isoMk {L L' : X.LineBundle} (e : L.toModules ≅ L'.toModules) : L ≅ L' :=
  { hom := e.hom
    inv := e.inv
    hom_inv_id := e.hom_inv_id
    inv_hom_id := e.inv_hom_id }

/-- An isomorphism of line bundles gives an isomorphism of the underlying modules. -/
def toModulesIso {L L' : X.LineBundle} (e : L ≅ L') : L.toModules ≅ L'.toModules :=
  (forget X).mapIso e

/-- Line bundles are isomorphic ⟺ the underlying modules are isomorphic. -/
theorem nonempty_iso_iff {L L' : X.LineBundle} : Nonempty (L ≅ L') ↔ Nonempty (L.toModules ≅ L'.toModules) :=
  ⟨fun ⟨e⟩ ↦ ⟨toModulesIso e⟩, fun ⟨e⟩ ↦ ⟨isoMk e⟩⟩

/-- The trivial line bundle `O_X`. -/
instance : One X.LineBundle := ⟨ofModules (SheafOfModules.unit X.ringCatSheaf)⟩

@[simp] theorem one_toModules : (1 : X.LineBundle).toModules = SheafOfModules.unit X.ringCatSheaf := rfl

/-- Pullback along any morphism. -/
def pullback (f : X ⟶ Y) (L : Y.LineBundle) : X.LineBundle :=
  ofModules ((Modules.pullback f).obj L.toModules)

@[simp] theorem pullback_toModules (f : X ⟶ Y) (L : Y.LineBundle) :
    (L.pullback f).toModules = (Modules.pullback f).obj L.toModules := rfl

/-- The pullback of the trivial line bundle is trivial (an explicit isomorphism). -/
def pullbackOneIso (f : X ⟶ Y) : (1 : Y.LineBundle).pullback f ≅ 1 :=
  isoMk (Modules.pullbackUnitIso f)

/-- Global sections. -/
abbrev sections (L : X.LineBundle) : Type u := Γ(L.toModules, ⊤)

end LineBundle

end AlgebraicGeometry.Scheme

end
