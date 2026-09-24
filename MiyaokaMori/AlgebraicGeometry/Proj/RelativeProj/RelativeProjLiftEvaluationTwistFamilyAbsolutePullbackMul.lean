import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap

/-! # Pulled-back sections and the strong monoidal structure of `f^*` (general identities)

Helper module for `RelativeProjLiftEvaluationTwistFamilyAbsolute.lean`. Everything is stated for an arbitrary morphism
`f : Y ⟶ X` and arbitrary modules; the twisting sheaves of `Proj` do not appear.

* `pullbackSectionsOn_map_app`: `(f^*k)(η x|_B) = η (k x)|_B` (naturality of the adjunction unit).
* `inv_pullbackTensorObjHom_app_tensorSections`: `δ⁻¹(η x|_B ⊗ η y|_B) = η(x ⊗ y)|_B`
  (from `pullbackTensorObjHom_app_unit_tensorSections`).
* `tensorIsoTensorObj_inv_app_tensorSections_tfa`: `(tensorIsoTensorObj M N).inv (x ⊗ y) = moduleTensorSection x y`.
* `pullbackMulHom_app_tensorSections`: for `m : Modules.tensor M N ⟶ P` the composite
  `δ⁻¹ ≫ f^*((tensorIsoTensorObj).inv ≫ m)` sends `η x|_B ⊗ η y|_B` to `η(m(x ⊗ y))|_B`. This is the shape of
  `Proj.TwistFamily.mulHom`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)

/-- A morphism of modules commutes with restriction (element form). -/
theorem hom_app_res_tfa {Z : AlgebraicGeometry.Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) {W W' : Z.Opens}
    (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- Naturality of the adjunction unit on sections: `(f^*k)(η_M x) = η_N (k x)`. -/
theorem pullbackUnitHom_map_app {M N : X.Modules} (k : M ⟶ N) (V : X.Opens) (x : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map k).app (f ⁻¹ᵁ V) (pullbackUnitHom f M V x) =
      pullbackUnitHom f N V (k.app V x) := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality k
  have h' := congrArg (fun q : M ⟶ (AlgebraicGeometry.Scheme.Modules.pullback f ⋙
      AlgebraicGeometry.Scheme.Modules.pushforward f).obj N => q.app V x) h
  exact h'.symm

/-- `(f^*k)(η_M x|_B) = η_N (k x)|_B`. -/
theorem pullbackSectionsOn_map_app {M N : X.Modules} (k : M ⟶ N) (V : X.Opens) (B : Y.Opens)
    (h : B ≤ f ⁻¹ᵁ V) (x : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map k).app B (pullbackSectionsOn f M V B h x) =
      pullbackSectionsOn f N V B h (k.app V x) := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply, hom_app_res_tfa, pullbackUnitHom_map_app]

end AlgebraicGeometry.Scheme.Modules


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)

/-- `(φ ≫ ψ).app U x = ψ.app U (φ.app U x)`. -/
theorem comp_app_apply' {Z : AlgebraicGeometry.Scheme.{u}} {A B C : Z.Modules} (φ : A ⟶ B) (ψ : B ⟶ C)
    (U : Z.Opens) (x : Γ(A, U)) : (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

/-- `(inv φ) (φ y) = y` on sections, for an isomorphism `φ` of modules. -/
theorem inv_app_app {Z : AlgebraicGeometry.Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) [IsIso φ] (U : Z.Opens)
    (y : Γ(M, U)) : (CategoryTheory.inv φ).app U (φ.app U y) = y := by
  change (φ.app U ≫ (CategoryTheory.inv φ).app U) y = y
  rw [← Hom.comp_app, IsIso.hom_inv_id, Hom.id_app]
  rfl

/-- `η_M x|_B ⊗ η_N y|_B = (η_M x ⊗ η_N y)|_B`. -/
theorem tensorSections_pullbackSectionsOn (M N : X.Modules) (V : X.Opens) (B : Y.Opens) (h : B ≤ f ⁻¹ᵁ V)
    (x : Γ(M, V)) (y : Γ(N, V)) :
    tensorSections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) B
        (pullbackSectionsOn f M V B h x) (pullbackSectionsOn f N V B h y) =
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := Y.Modules)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)).presheaf.map (homOfLE h).op
        (tensorSections _ _ (f ⁻¹ᵁ V) (pullbackUnitHom f M V x) (pullbackUnitHom f N V y)) :=
  (tensorSections_restrict _ _ (homOfLE h) (pullbackUnitHom f M V x) (pullbackUnitHom f N V y)).symm

/-- `δ⁻¹(η_M x ⊗ η_N y) = η_{M ⊗ N}(x ⊗ y)` on `f⁻¹V`. -/
theorem inv_pullbackTensorObjHom_app_unit_tensorSections (M N : X.Modules) (V : X.Opens)
    (x : Γ(M, V)) (y : Γ(N, V)) :
    (CategoryTheory.inv (pullbackTensorObjHom f M N)).app (f ⁻¹ᵁ V)
        (tensorSections _ _ (f ⁻¹ᵁ V) (pullbackUnitHom f M V x) (pullbackUnitHom f N V y)) =
      pullbackUnitHom f (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N) V
        (tensorSections M N V x y) := by
  have hδ := pullbackTensorObjHom_app_unit_tensorSections f M N V x y
  change (pullbackTensorObjHom f M N).app (f ⁻¹ᵁ V)
    (pullbackUnitHom f (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) V (tensorSections M N V x y)) =
    tensorSections _ _ (f ⁻¹ᵁ V) (pullbackUnitHom f M V x) (pullbackUnitHom f N V y) at hδ
  exact (congrArg (fun z => (CategoryTheory.inv (pullbackTensorObjHom f M N)).app (f ⁻¹ᵁ V) z) hδ.symm).trans
    (inv_app_app (pullbackTensorObjHom f M N) (f ⁻¹ᵁ V) _)

/-- `δ⁻¹(η_M x|_B ⊗ η_N y|_B) = η_{M ⊗ N}(x ⊗ y)|_B`. -/
theorem inv_pullbackTensorObjHom_app_tensorSections (M N : X.Modules) (V : X.Opens) (B : Y.Opens)
    (h : B ≤ f ⁻¹ᵁ V) (x : Γ(M, V)) (y : Γ(N, V)) :
    (CategoryTheory.inv (pullbackTensorObjHom f M N)).app B
        (tensorSections _ _ B (pullbackSectionsOn f M V B h x) (pullbackSectionsOn f N V B h y)) =
      pullbackSectionsOn f (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N) V B h
        (tensorSections M N V x y) :=
  (congrArg (fun z => (CategoryTheory.inv (pullbackTensorObjHom f M N)).app B z)
      (tensorSections_pullbackSectionsOn f M N V B h x y)).trans
    ((hom_app_res_tfa (CategoryTheory.inv (pullbackTensorObjHom f M N)) h _).trans
      (congrArg (fun z => ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N)).presheaf.map (homOfLE h).op z)
        (inv_pullbackTensorObjHom_app_unit_tensorSections f M N V x y)))

/-- `(tensorIsoTensorObj M N).inv (x ⊗ y) = moduleTensorSection x y` (the pure-tensor section of
`Modules.tensor M N`). -/
theorem tensorIsoTensorObj_inv_app_tensorSections_tfa {Z : AlgebraicGeometry.Scheme.{u}} (M N : Z.Modules)
    (V : Z.Opens) (x : Γ(M, V)) (y : Γ(N, V)) :
    (tensorIsoTensorObj M N).inv.app V (tensorSections M N V x y) = AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y :=
  tensorToSheafify_tensorSections M N V x y

/-- **The shape of `Proj.TwistFamily.mulHom` on pulled-back sections.** For `m : Modules.tensor M N ⟶ P`,
`(δ⁻¹ ≫ f^*((tensorIsoTensorObj M N).inv ≫ m))(η x|_B ⊗ η y|_B) = η(m(x ⊗ y))|_B`. -/
theorem pullbackMulHom_app_tensorSections (M N P : X.Modules)
    (m : AlgebraicGeometry.Scheme.Modules.tensor M N ⟶ P) (V : X.Opens) (B : Y.Opens) (h : B ≤ f ⁻¹ᵁ V)
    (x : Γ(M, V)) (y : Γ(N, V)) :
    (CategoryTheory.inv (pullbackTensorObjHom f M N) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map ((tensorIsoTensorObj M N).inv ≫ m)).app B
        (tensorSections _ _ B (pullbackSectionsOn f M V B h x) (pullbackSectionsOn f N V B h y)) =
      pullbackSectionsOn f P V B h (m.app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) :=
  (congrArg (fun z => ((AlgebraicGeometry.Scheme.Modules.pullback f).map ((tensorIsoTensorObj M N).inv ≫ m)).app B z)
      (inv_pullbackTensorObjHom_app_tensorSections f M N V B h x y)).trans
    ((pullbackSectionsOn_map_app f ((tensorIsoTensorObj M N).inv ≫ m) V B h (tensorSections M N V x y)).trans
      (congrArg (fun z => pullbackSectionsOn f P V B h (m.app V z))
        (tensorIsoTensorObj_inv_app_tensorSections_tfa M N V x y)))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)

/-- Restricting the source open of a pulled-back section: `η_V g|_{B'} = η_W (g|_W)|_{B'}` for `W ≤ V`,
`B' ≤ f⁻¹W`. -/
theorem pullbackSectionsOn_res_source (M : X.Modules) {V W : X.Opens} (hWV : W ≤ V) {B' : Y.Opens}
    (h₁ : B' ≤ f ⁻¹ᵁ V) (h₂ : B' ≤ f ⁻¹ᵁ W) (g : Γ(M, V)) :
    pullbackSectionsOn f M V B' h₁ g = pullbackSectionsOn f M W B' h₂ (M.presheaf.map (homOfLE hWV).op g) := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply, pullbackUnitHom_restrict, famRes_comp']

/-- `pullbackSectionsOn` sends `0` to `0`. -/
theorem pullbackSectionsOn_zero (M : X.Modules) (V : X.Opens) (B' : Y.Opens) (h : B' ≤ f ⁻¹ᵁ V) :
    pullbackSectionsOn f M V B' h 0 = 0 :=
  map_zero (pullbackSectionsOn f M V B' h)

end AlgebraicGeometry.Scheme.Modules

end
