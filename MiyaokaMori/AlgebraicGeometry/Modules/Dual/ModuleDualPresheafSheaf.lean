import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual
import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Compatible local dual functionals already form a sheaf

The original `LocalDualSections` glue as additive natural transformations.
Linearity over the structure sheaf is checked on the pulled-back covering sieve,
using the separatedness of the actual structure sheaf. Thus the original
`moduleDualPresheaf` is a sheaf before sheafification.

Source: Stacks Project, `modules.tex`, section `Internal Hom`. This is a prerequisite for the
dual-anticanonical comparison over the same module objects, not a replacement degree definition.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.ModuleDualPresheafSheaf

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (M : X.Modules)

private abbrev structureAdditive : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (SheafOfModules.unit X.ringCatSheaf).val.presheaf

private def functionalToHom (U : X.Opens) (φ : LocalDualSections X M U) :
    (presheafHom M.presheaf (structureAdditive (X := X))).obj (op U) where
  app V := AddCommGrpCat.ofHom (φ.val V.unop).toAddMonoidHom
  naturality V W i := by
    ext x
    exact φ.property W.unop V.unop i.unop x

private def evalSection {U : X.Opens}
    (α : (presheafHom M.presheaf (structureAdditive (X := X))).obj (op U))
    (V : Over U) (s : Γ(M, V.left)) : Γ(X, V.left) :=
  (α.app (op V)).hom s

private theorem functionalToHom_injective (U : X.Opens) :
    Function.Injective (functionalToHom M U) := by
  intro φ ψ h
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom (congrArg (fun α ↦ α.app (op V)) h) x

private def toHom :
    (moduleDualPresheaf M).presheaf ⋙ CategoryTheory.forget AddCommGrpCat ⟶
      presheafHom M.presheaf (structureAdditive (X := X)) where
  app U := ↾(functionalToHom M U.unop)
  naturality U V i := by
    ext φ W x
    rfl

private theorem hom_apply_restrict {U : X.Opens}
    (α : (presheafHom M.presheaf (structureAdditive (X := X))).obj (op U))
    (V W : Over U) (i : V ⟶ W) (x : Γ(M, W.left)) :
    α.app (op V) (M.presheaf.map i.left.op x) =
      X.presheaf.map i.left.op (α.app (op W) x) :=
  ConcreteCategory.congr_hom (α.naturality i.op) x

private theorem amalgamation_linear {U : X.Opens} (S : Sieve U)
    (hS : S ∈ Opens.grothendieckTopology X U)
    (x : Presieve.FamilyOfElements
      ((moduleDualPresheaf M).presheaf ⋙ CategoryTheory.forget AddCommGrpCat) S.arrows)
    (hx : x.Compatible)
    (α : (presheafHom M.presheaf (structureAdditive (X := X))).obj (op U))
    (hα : (x.map (toHom M)).IsAmalgamation α)
    (V : Over U) (r : Γ(X, V.left)) (s : Γ(M, V.left)) :
    evalSection M α V (r • s) = r * evalSection M α V s := by
  have hOadd : Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (structureAdditive (X := X)) := by
    simpa only [structureAdditive] using (SheafOfModules.unit X.ringCatSheaf).isSheaf
  have hO : Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (structureAdditive (X := X) ⋙ CategoryTheory.forget AddCommGrpCat) := by
    exact (Presheaf.isSheaf_iff_isSheaf_comp
      (J := Opens.grothendieckTopology X) (P := structureAdditive (X := X))
      (CategoryTheory.forget AddCommGrpCat)).mp hOadd
  have hOs : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (structureAdditive (X := X) ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type (J := Opens.grothendieckTopology X)
      (structureAdditive (X := X) ⋙ CategoryTheory.forget AddCommGrpCat)).mp hO
  apply (hOs (S.pullback V.hom)
    ((Opens.grothendieckTopology X).pullback_stable V.hom hS)).isSeparatedFor.ext
  intro W j hj
  let WU : Over U := Over.mk (j ≫ V.hom)
  let jV : WU ⟶ V := Over.homMk j
  have hloc : α.app (op WU) =
      (functionalToHom M W (x (j ≫ V.hom) hj)).app (op (Over.mk (𝟙 W))) := by
    exact (PresheafHom.isAmalgamation_iff _ _ (hx.map (toHom M)) α).mp hα
      W (j ≫ V.hom) hj
  have hnat₁ := ConcreteCategory.congr_hom (α.naturality jV.op) (r • s)
  have hnat₂ := ConcreteCategory.congr_hom (α.naturality jV.op) s
  have hnat₁' :
      (α.app (op WU)).hom (M.presheaf.map j.op (r • s)) =
        X.presheaf.map j.op ((α.app (op V)).hom (r • s)) := by
    change (α.app (op WU)).hom (M.presheaf.map j.op (r • s)) =
      X.presheaf.map j.op ((α.app (op V)).hom (r • s)) at hnat₁
    exact hnat₁
  have hnat₂' :
      (α.app (op WU)).hom (M.presheaf.map j.op s) =
        X.presheaf.map j.op ((α.app (op V)).hom s) := by
    change (α.app (op WU)).hom (M.presheaf.map j.op s) =
      X.presheaf.map j.op ((α.app (op V)).hom s) at hnat₂
    exact hnat₂
  have hnat₁'' :
      (α.app (op WU)).hom (M.presheaf.map j.op (r • s)) =
        X.presheaf.map j.op (evalSection M α V (r • s)) := hnat₁'
  have hnat₂'' :
      (α.app (op WU)).hom (M.presheaf.map j.op s) =
        X.presheaf.map j.op (evalSection M α V s) := hnat₂'
  change X.presheaf.map j.op (evalSection M α V (r • s)) =
    X.presheaf.map j.op (r * evalSection M α V s)
  rw [← hnat₁'', map_mul, ← hnat₂'', hloc]
  change (x (j ≫ V.hom) hj).val (Over.mk (𝟙 W))
      (M.presheaf.map j.op (r • s)) =
    (X.presheaf.map j.op r : Γ(X, W)) *
      (show Γ(X, W) from
        (x (j ≫ V.hom) hj).val (Over.mk (𝟙 W)) (M.presheaf.map j.op s))
  rw [M.map_smul]
  exact ((x (j ≫ V.hom) hj).val (Over.mk (𝟙 W))).map_smul _ _

/-- The original presheaf of compatible local linear functionals is a sheaf,
without a local-freeness or affine hypothesis. -/
theorem moduleDualPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (moduleDualPresheaf M).presheaf := by
  apply (Presheaf.isSheaf_iff_isSheaf_comp
    (J := Opens.grothendieckTopology X) (P := (moduleDualPresheaf M).presheaf)
    (CategoryTheory.forget AddCommGrpCat)).mpr
  apply (CategoryTheory.isSheaf_iff_isSheaf_of_type
    (J := Opens.grothendieckTopology X)
    ((moduleDualPresheaf M).presheaf ⋙ CategoryTheory.forget AddCommGrpCat)).mpr
  intro U S hS x hx
  have hHom := CategoryTheory.Presheaf.IsSheaf.hom M.presheaf
    (structureAdditive (X := X)) (SheafOfModules.unit X.ringCatSheaf).isSheaf
  obtain ⟨α, hα, huniq⟩ := hHom.isSheafFor S hS (x.map (toHom M)) (hx.map (toHom M))
  let φ : LocalDualSections X M U :=
    ⟨fun V ↦
      { toFun := fun s ↦ evalSection M α V s
        map_add' := by
          intro s₁ s₂
          change (α.app (op V)).hom (s₁ + s₂) =
            (α.app (op V)).hom s₁ + (α.app (op V)).hom s₂
          exact (α.app (op V)).hom.map_add _ _
        map_smul' := amalgamation_linear M S hS x hx α hα V }, by
      intro V W i s
      exact hom_apply_restrict M α V W i s⟩
  have hφ : functionalToHom M U φ = α := by
    apply NatTrans.ext
    ext V s
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro V j hj
    apply functionalToHom_injective M V
    change (toHom M).app (op V)
        (((moduleDualPresheaf M).presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map j.op φ) = _
    rw [NatTrans.naturality_apply]
    change (presheafHom M.presheaf (structureAdditive (X := X))).map j.op
      (functionalToHom M U φ) = functionalToHom M V (x j hj)
    rw [hφ]
    exact hα j hj
  · intro ψ hψ
    apply functionalToHom_injective M U
    rw [hφ]
    exact huniq (functionalToHom M U ψ) (hψ.map (toHom M))

end AlgebraicGeometry.Scheme.Modules.ModuleDualPresheafSheaf
