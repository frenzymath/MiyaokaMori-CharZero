import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The canonical tensor-to-stalk map for module pullback

The unit of the actual module pullback/pushforward adjunction gives a semilinear
map from the source module stalk to the stalk of its actual pullback.  Extension
of scalars along the specified scheme stalk map then gives a linear map from the
corresponding tensor product.  The construction records the unit and pure-tensor
germ formulas without asserting that this map is an isomorphism.

The source is Stacks Project, `sheaves.tex`, lemma `stalk-pullback-modules`.
No finite-presentation, flatness, local-freeness, or nonemptiness hypothesis is
used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false

/-- The algebra structure induced by the actual map on local rings. -/
@[instance_reducible]
def modulePullbackStalkAlgebra (x : X) :
    Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

attribute [local instance] modulePullbackStalkAlgebra

/-- The actual abelian stalk of the module pullback. -/
abbrev modulePullbackStalk (M : Y.Modules) (x : X) :
    AddCommGrpCat.{u} := ((Scheme.Modules.pullback f).obj M).presheaf.stalk x

/-- The adjunction unit followed by the genuine pushforward stalk map. -/
def modulePullbackStalkUnitAddHom (M : Y.Modules) (x : X) :
    M.presheaf.stalk (f x) →+
      modulePullbackStalk f M x :=
  ((TopCat.Presheaf.stalkFunctor Ab (f x)).map
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val) ≫
    TopCat.Presheaf.stalkPushforward Ab f.base
      ((Scheme.Modules.pullback f).obj M).val.presheaf x).hom

set_option backward.isDefEq.respectTransparency false in
/-- The stalk unit sends a source germ to the germ of the adjunction-unit section. -/
@[simp]
theorem modulePullbackStalkUnitAddHom_germ (M : Y.Modules) (x : X)
    (U : Y.Opens) (hx : f x ∈ U) (m : M.val.obj (op U)) :
    modulePullbackStalkUnitAddHom f M x
        (M.presheaf.germ U (f x) hx m) =
      ((Scheme.Modules.pullback f).obj M).presheaf.germ
        (f ⁻¹ᵁ U) x hx
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m) := by
  change (TopCat.Presheaf.stalkPushforward Ab f.base
      ((Scheme.Modules.pullback f).obj M).val.presheaf x)
    (((TopCat.Presheaf.stalkFunctor Ab (f x)).map
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val))
      (M.presheaf.germ U (f x) hx m)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact TopCat.Presheaf.stalkPushforward_germ_apply Ab f.base
    ((Scheme.Modules.pullback f).obj M).val.presheaf U x hx
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m)

/-- The stalk unit is semilinear for the actual local-ring homomorphism. -/
theorem modulePullbackStalkUnitAddHom_smul (M : Y.Modules) (x : X)
    (r : Y.presheaf.stalk (f x)) (m : M.presheaf.stalk (f x)) :
    modulePullbackStalkUnitAddHom f M x (r • m) =
      f.stalkMap x r • modulePullbackStalkUnitAddHom f M x m := by
  obtain ⟨U, hxU, a, rfl⟩ := Y.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [← Y.presheaf.germ_res_apply (CategoryTheory.homOfLE hVU) (f x) hxV a]
  erw [← PresheafOfModules.germ_smul (R := Y.presheaf) M.val,
    modulePullbackStalkUnitAddHom_germ,
    Scheme.Modules.Hom.app_smul,
    PresheafOfModules.germ_smul (R := X.presheaf)
      ((Scheme.Modules.pullback f).obj M).val,
    Scheme.Hom.germ_stalkMap_apply,
    modulePullbackStalkUnitAddHom_germ]
  rfl

/-- The genuine semilinear stalk map induced by the module pullback unit. -/
def modulePullbackStalkUnit (M : Y.Modules) (x : X) :
    M.presheaf.stalk (f x) →ₛₗ[(f.stalkMap x).hom]
      modulePullbackStalk f M x where
  toAddHom := modulePullbackStalkUnitAddHom f M x
  map_smul' := modulePullbackStalkUnitAddHom_smul f M x

/-- The scalar extension of the original module stalk at a point of `X`. -/
abbrev modulePullbackStalkTensor (M : Y.Modules) (x : X) :=
  X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] M.presheaf.stalk (f x)

private def modulePullbackStalkUnitLinear (M : Y.Modules) (x : X) :
    letI := Module.compHom (modulePullbackStalk f M x) (f.stalkMap x).hom
    M.presheaf.stalk (f x) →ₗ[Y.presheaf.stalk (f x)] modulePullbackStalk f M x := by
  letI := Module.compHom (modulePullbackStalk f M x) (f.stalkMap x).hom
  exact { modulePullbackStalkUnit f M x with
    map_smul' := modulePullbackStalkUnitAddHom_smul f M x }

set_option backward.isDefEq.respectTransparency false in
/-- The canonical linear map from the local scalar extension to the pullback stalk. -/
def modulePullbackStalkTensorMap (M : Y.Modules) (x : X) :
    modulePullbackStalkTensor f M x →ₗ[X.presheaf.stalk x]
      modulePullbackStalk f M x := by
  letI := Module.compHom (modulePullbackStalk f M x) (f.stalkMap x).hom
  letI : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (modulePullbackStalk f M x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s ↦ s • modulePullbackStalkUnitLinear f M x
      map_add' := fun s t ↦ by ext m; simp [add_smul]
      map_smul' := fun s t ↦ by ext m; simp [mul_smul] }

/-- On pure tensors the map is scalar multiplication of the genuine stalk unit. -/
@[simp]
theorem modulePullbackStalkTensorMap_tmul (M : Y.Modules) (x : X)
    (s : X.presheaf.stalk x) (m : M.presheaf.stalk (f x)) :
    modulePullbackStalkTensorMap f M x (s ⊗ₜ[Y.presheaf.stalk (f x)] m) =
      s • modulePullbackStalkUnit f M x m := rfl

/-- On a local source section, the pure-tensor map has the expected germ formula. -/
theorem modulePullbackStalkTensorMap_tmul_germ (M : Y.Modules) (x : X)
    (s : X.presheaf.stalk x) (U : Y.Opens) (hx : f x ∈ U)
    (m : M.val.obj (op U)) :
    modulePullbackStalkTensorMap f M x
        (s ⊗ₜ[Y.presheaf.stalk (f x)] M.presheaf.germ U (f x) hx m) =
      s • ((Scheme.Modules.pullback f).obj M).presheaf.germ
        (f ⁻¹ᵁ U) x hx
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m) := by
  rw [modulePullbackStalkTensorMap_tmul]
  exact congrArg (s • ·) (modulePullbackStalkUnitAddHom_germ f M x U hx m)

end AlgebraicGeometry.Scheme.Modules
