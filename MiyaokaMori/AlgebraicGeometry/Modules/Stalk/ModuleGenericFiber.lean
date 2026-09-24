import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Stalk maps and the generic fiber of a module sheaf

The abelian stalk of a module sheaf carries Mathlib's canonical action of the local ring.
Maps of module sheaves are linear on these stalks, while specialization is semilinear
over the corresponding map of local rings. On an integral scheme, specialization to
the generic point gives the canonical map from each stalk to the generic fiber.

These maps supply the generic-fiber interface for saturating a rational line in the
same module sheaf, as used in the paper. They do not assert existence
of a saturated subsheaf or a line filtration.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical local-ring action on the actual stalk of a module sheaf. -/
instance moduleStalkModule (X : Scheme.{u}) (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  change Module (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (C := Ab)
      (show _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) from M.val).presheaf x)
  infer_instance

/-- The usual map of abelian stalks, linear over the actual local ring. -/
def moduleStalkMap (X : Scheme.{u}) (x : X) {M N : X.Modules} (f : M ⟶ N) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  toFun := (TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, b, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (CategoryTheory.homOfLE hVU) x hxV a]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) M.val,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.presheaf.germ V x hxV (f.app V (_ • b)) = _
    erw [Scheme.Modules.Hom.app_smul, PresheafOfModules.germ_smul (R := X.presheaf) N.val,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl

/-- Taking the actual stalk as a module over its local ring. -/
def moduleStalkFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat (X.presheaf.stalk x) where
  obj M := ModuleCat.of _ (M.presheaf.stalk x)
  map f := ModuleCat.ofHom (moduleStalkMap X x f)
  map_id M := by
    ext m
    exact CategoryTheory.congr_fun (C := AddCommGrpCat.{u})
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_id M) m
  map_comp f g := by
    ext m
    exact CategoryTheory.congr_fun (C := AddCommGrpCat.{u})
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp f g) m

/-- On germs the linear stalk map is the germ of the original map on sections. -/
@[simp]
theorem moduleStalkMap_germ (X : Scheme.{u}) (x : X) {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    moduleStalkMap X x f (M.presheaf.germ U x hx m) =
      N.presheaf.germ U x hx (f.app U m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.mapPresheaf m

/-- The actual specialization map of a module sheaf, semilinear over the map of local rings. -/
def moduleStalkSpecializes (X : Scheme.{u}) (M : X.Modules) {x y : X} (h : x ⤳ y) :
    M.presheaf.stalk y →ₛₗ[(X.presheaf.stalkSpecializes h).hom] M.presheaf.stalk x where
  toFun := M.presheaf.stalkSpecializes h
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hyU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hyV, b, rfl⟩ := M.presheaf.exists_le_germ_eq m hyU
    rw [← X.presheaf.germ_res_apply (CategoryTheory.homOfLE hVU) y hyV a]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) M.val,
      TopCat.Presheaf.germ_stalkSpecializes_apply,
      TopCat.Presheaf.germ_stalkSpecializes_apply,
      TopCat.Presheaf.germ_stalkSpecializes_apply,
      PresheafOfModules.germ_smul (R := X.presheaf) M.val]
    rfl

/-- Specialization preserves the representative section of a germ. -/
@[simp]
theorem moduleStalkSpecializes_germ (X : Scheme.{u}) (M : X.Modules) {x y : X}
    (h : x ⤳ y) (U : X.Opens) (hy : y ∈ U) (m : Γ(M, U)) :
    moduleStalkSpecializes X M h (M.presheaf.germ U y hy m) =
      M.presheaf.germ U x (h.mem_open U.isOpen hy) m :=
  TopCat.Presheaf.germ_stalkSpecializes_apply M.presheaf hy h m

/-- Maps of module sheaves commute with the actual specialization maps on stalks. -/
theorem moduleStalkSpecializes_naturality (X : Scheme.{u}) {M N : X.Modules}
    (f : M ⟶ N) {x y : X} (h : x ⤳ y) (m : M.presheaf.stalk y) :
    moduleStalkMap X x f (moduleStalkSpecializes X M h m) =
      moduleStalkSpecializes X N h (moduleStalkMap X y f m) :=
  TopCat.Presheaf.stalkSpecializes_stalkFunctor_map_apply f.mapPresheaf h m

/-- The canonical map from a module stalk to its stalk at the generic point. -/
def moduleStalkToGenericFiber (X : Scheme.{u}) [IsIntegral X] (M : X.Modules) (x : X) :
    M.presheaf.stalk x →ₛₗ[algebraMap (X.presheaf.stalk x) X.functionField]
      M.presheaf.stalk (genericPoint X) :=
  moduleStalkSpecializes X M ((genericPoint_spec X).specializes trivial)

/-- The canonical generic-fiber map sends a germ to the same section's generic germ. -/
@[simp]
theorem moduleStalkToGenericFiber_germ (X : Scheme.{u}) [IsIntegral X] (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    moduleStalkToGenericFiber X M x (M.presheaf.germ U x hx m) =
      M.presheaf.germ U (genericPoint X)
        (((genericPoint_spec X).specializes trivial).mem_open U.isOpen hx) m :=
  moduleStalkSpecializes_germ X M _ U hx m

/-- The canonical generic-fiber map is natural in the actual module sheaf. -/
theorem moduleStalkToGenericFiber_naturality (X : Scheme.{u}) [IsIntegral X]
    {M N : X.Modules} (f : M ⟶ N) (x : X) (m : M.presheaf.stalk x) :
    moduleStalkMap X (genericPoint X) f (moduleStalkToGenericFiber X M x m) =
      moduleStalkToGenericFiber X N x (moduleStalkMap X x f m) :=
  moduleStalkSpecializes_naturality X f _ m

end AlgebraicGeometry.Scheme.Modules
