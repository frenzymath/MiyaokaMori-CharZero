import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The dual of a sheaf of modules

Over each open set, take families of local linear functionals compatible with
restriction to smaller opens. Scalar restriction makes these families a presheaf
of modules; its sheafification defines `moduleSheafDual`.

This is the canonical dual construction supporting the tangent sheaves of §§1–2 of the paper.
No local-freeness, duality equivalence, tangent exactness, or degree theorem is asserted here.

Sources: the Stacks Project, sheaves of modules and internal Hom; Mathlib's module sheafification
construction.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Classical

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A linear functional on sections over an open set contained in `U`. -/
abbrev LocalFunctional (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) (V : Over U) :=
  Γ(M, V.left) →ₗ[Γ(X, V.left)] Γ(X, V.left)

/-- Scalars on `U` act on local functionals through the restriction homomorphism. -/
instance localFunctionalModule (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (V : Over U) : Module Γ(X, U) (LocalFunctional X M U V) :=
  Module.compHom _ (X.presheaf.map V.hom.op).hom

/-- A family of linear functionals indexed by the opens contained in `U`. -/
abbrev LocalFunctionalFamily (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :=
  (V : Over U) → LocalFunctional X M U V

/-- Families of local linear functionals that commute with every restriction. -/
def localDualSubmodule (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :
    Submodule Γ(X, U) (LocalFunctionalFamily X M U) where
  carrier := {φ | ∀ (V W : Over U) (i : V ⟶ W) (x : Γ(M, W.left)),
    φ V (M.presheaf.map i.left.op x) = X.presheaf.map i.left.op (φ W x)}
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ V W i x
    simpa using congrArg₂ (· + ·) (hφ V W i x) (hψ V W i x)
  smul_mem' := by
    intro r φ hφ V W i x
    change X.presheaf.map V.hom.op r * φ V (M.presheaf.map i.left.op x) =
      X.presheaf.map i.left.op (X.presheaf.map W.hom.op r * φ W x)
    rw [map_mul, hφ V W i x]
    congr 1
    have h : V.hom = i.left ≫ W.hom := (Over.w i).symm
    rw [h, op_comp, X.presheaf.map_comp]
    rfl

/-- Compatible local functionals over `U`, as a module of sections. -/
abbrev LocalDualSections (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :=
  localDualSubmodule X M U

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a compatible family of local functionals to a smaller open. -/
def localDualRestrict {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    LocalDualSections X M U →ₛₗ[(X.presheaf.map i.op).hom] LocalDualSections X M V where
  toFun φ := ⟨fun W ↦ φ.1 ((Over.map i).obj W), by
    intro W Z j x
    exact φ.2 ((Over.map i).obj W) ((Over.map i).obj Z) ((Over.map i).map j) x⟩
  map_add' φ ψ := rfl
  map_smul' r φ := by
    apply Subtype.ext
    funext W
    ext x
    change (X.presheaf.map (W.hom ≫ i).op r : Γ(X, W.left)) *
        (show Γ(X, W.left) from φ.1 ((Over.map i).obj W) x) =
      X.presheaf.map W.hom.op (X.presheaf.map i.op r) *
        (show Γ(X, W.left) from φ.1 ((Over.map i).obj W) x)
    rw [op_comp, X.presheaf.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
private def moduleDualMap {X : Scheme.{u}} (M : X.Modules) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    ModuleCat.of _ (LocalDualSections X M U.unop) ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
        (ModuleCat.of _ (LocalDualSections X M V.unop)) :=
  ModuleCat.ofHom (Y :=
    (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of _ (LocalDualSections X M V.unop)))
    { toFun := localDualRestrict M i.unop
      map_add' := (localDualRestrict M i.unop).map_add
      map_smul' := (localDualRestrict M i.unop).map_smulₛₗ }

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf of compatible local linear functionals. -/
def moduleDualPresheaf {X : Scheme.{u}} (M : X.Modules) : X.PresheafOfModules where
  obj U := ModuleCat.of _ (LocalDualSections X M U.unop)
  map {U V} i := moduleDualMap M i
  map_id U := by
    ext φ
    rfl
  map_comp i j := by
    ext φ
    rfl

/-- The dual module sheaf, formed by sheafifying compatible local functionals. -/
def moduleSheafDual {X : Scheme.{u}} (M : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (moduleDualPresheaf M)

end AlgebraicGeometry.Scheme.Modules
