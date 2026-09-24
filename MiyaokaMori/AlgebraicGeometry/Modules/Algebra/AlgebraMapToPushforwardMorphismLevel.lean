import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPushforwardLaxSections
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # Algebra maps to a pushforward structure sheaf, at the level of morphisms

`IsAlgebraMapToPushforward` (`RelativeSpecUniversalProperty`) is stated on sections: `φ(a·b) = φ(a)·φ(b)` on
`tensorSections a b` and `φ(1) = 1`. This file gives the equivalent **morphism-level** formulations and the
adjoint transposition needed to check them after pulling back:

* `pushforwardUnitMul g : g_*O_T ⊗ g_*O_T ⟶ g_*O_T` is `μ_{g_*} ≫ g_*(λ_ O_T).hom`; on section pairs it is the
  ring multiplication of `Γ(T, g⁻¹U)` (`pushforwardUnitMul_app_tensorSections`, from
  `pushforwardLaxMonoidal_μ_tensorSections` and `leftUnitor_app_tensorSections`).
* `mul_comp_eq_of_isAlgebraMap_mul` / `isAlgebraMap_mul_of_mul_comp`: the multiplicativity clause of
  `IsAlgebraMapToPushforward` is equivalent to `A.mul ≫ φ = (φ ⊗ₘ φ) ≫ pushforwardUnitMul g`
  (`tensorObj_hom_ext`: morphisms out of a tensor product are determined on section pairs; `tensorHom_tensorSections`).
* `unit_hom_ext`: two morphisms `O_X ⟶ N` agreeing on `1` agree (`O_X`-linearity, `Hom.app_smul`), so the unit
  clause gives `A.one ≫ φ₁ = A.one ≫ φ₂` (`one_comp_eq_of_isAlgebraMap_one`).
* `tensorHom_homEquiv_pushforwardUnitMul`: for `a : g^*M ⟶ O_T`, `b : g^*N ⟶ O_T`,
  `(homEquiv a ⊗ₘ homEquiv b) ≫ pushforwardUnitMul g = homEquiv (δ_{M,N} ≫ (a ⊗ₘ b) ≫ (λ_ O_T).hom)`
  (`homEquiv_pullbackTensorObjHom`: `δ` transposes to `(η ⊗ η) ≫ μ`; `μ_natural`; `homEquiv_naturality_right`).

Source: Stacks 01LQ (maps to a relative Spec are algebra maps).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- Two morphisms out of `O_X` agreeing on the unit sections agree. -/
theorem unit_hom_ext {N : X.Modules} {f g : 𝟙_ X.Modules ⟶ N}
    (h : ∀ U : X.Opens, f.app U (1 : Γ(X, U)) = g.app U (1 : Γ(X, U))) : f = g := by
  ext U r
  let r' : Γ(X, U) := r
  let e : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))
  calc f.app U r = f.app U (r' • e) := congrArg _ (mul_one r').symm
    _ = r' • f.app U e := Hom.app_smul f r' e
    _ = r' • g.app U e := congrArg (fun z => r' • z) (h U)
    _ = g.app U (r' • e) := (Hom.app_smul g r' e).symm
    _ = g.app U r := congrArg _ (mul_one r')

/-- The multiplication `g_*O_T ⊗ g_*O_T ⟶ g_*O_T`: `μ_{g_*}` followed by `g_*` of the left unitor. -/
def pushforwardUnitMul (g : T ⟶ X) :
    (pushforward g).obj (𝟙_ T.Modules) ⊗ (pushforward g).obj (𝟙_ T.Modules) ⟶
      (pushforward g).obj (𝟙_ T.Modules) :=
  letI := pushforwardLaxMonoidal g
  CategoryTheory.Functor.LaxMonoidal.μ (pushforward g) (𝟙_ T.Modules) (𝟙_ T.Modules) ≫
    (pushforward g).map (λ_ (𝟙_ T.Modules)).hom

/-- On section pairs, `pushforwardUnitMul` is the multiplication of `Γ(T, g⁻¹U)`. -/
theorem pushforwardUnitMul_val_app_tensorSections (g : T ⟶ X) (U : X.Opens) (a b : Γ(T, g ⁻¹ᵁ U)) :
    (pushforwardUnitMul g).val.app (Opposite.op U)
      (tensorSections ((pushforward g).obj (𝟙_ T.Modules))
        ((pushforward g).obj (𝟙_ T.Modules)) U a b) = a * b := by
  let _ := pushforwardLaxMonoidal g
  have h1 := pushforwardLaxMonoidal_μ_tensorSections g (SheafOfModules.unit T.ringCatSheaf)
    (SheafOfModules.unit T.ringCatSheaf) U a b
  have h1' : (CategoryTheory.Functor.LaxMonoidal.μ (pushforward g) (𝟙_ T.Modules)
        (𝟙_ T.Modules)).val.app (Opposite.op U)
        (tensorSections ((pushforward g).obj (𝟙_ T.Modules)) ((pushforward g).obj (𝟙_ T.Modules))
          U a b) =
      tensorSections (𝟙_ T.Modules) (𝟙_ T.Modules) (g ⁻¹ᵁ U) a b := h1
  have h2 : (λ_ (𝟙_ T.Modules)).hom.val.app (Opposite.op (g ⁻¹ᵁ U))
      (tensorSections (𝟙_ T.Modules) (𝟙_ T.Modules) (g ⁻¹ᵁ U) a b) = a * b :=
    leftUnitor_app_tensorSections (𝟙_ T.Modules) (g ⁻¹ᵁ U) a b
  show ((pushforward g).map (λ_ (𝟙_ T.Modules)).hom).val.app (Opposite.op U)
    ((CategoryTheory.Functor.LaxMonoidal.μ (pushforward g) (𝟙_ T.Modules) (𝟙_ T.Modules)).val.app
      (Opposite.op U)
      (tensorSections ((pushforward g).obj (𝟙_ T.Modules)) ((pushforward g).obj (𝟙_ T.Modules))
        U a b)) = a * b
  rw [h1']
  exact h2

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.QCAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (g : T ⟶ X)
  (φ : A.carrier ⟶ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))

/-- `((φ ⊗ₘ φ) ≫ pushforwardUnitMul g)(a ⊗ b) = φ(a) · φ(b)`. -/
theorem tensorHom_pushforwardUnitMul_val_app_tensorSections (U : X.Opens)
    (a b : A.carrier.val.obj (Opposite.op U)) :
    ((φ ⊗ₘ φ) ≫ pushforwardUnitMul g).val.app (Opposite.op U)
        (tensorSections A.carrier A.carrier U a b) =
      (show Γ(T, g ⁻¹ᵁ U) from φ.val.app (Opposite.op U) a) *
        (show Γ(T, g ⁻¹ᵁ U) from φ.val.app (Opposite.op U) b) := by
  show (pushforwardUnitMul g).val.app (Opposite.op U)
    ((φ ⊗ₘ φ).val.app (Opposite.op U) (tensorSections A.carrier A.carrier U a b)) = _
  rw [tensorHom_tensorSections]
  exact pushforwardUnitMul_val_app_tensorSections g U _ _

/-- Section-level multiplicativity ⇒ morphism-level: `A.mul ≫ φ = (φ ⊗ₘ φ) ≫ pushforwardUnitMul g`. -/
theorem mul_comp_eq_of_isAlgebraMap_mul
    (hφ : ∀ (U : X.Opens) (a b : A.carrier.val.obj (Opposite.op U)),
      (show Γ(T, g ⁻¹ᵁ U) from φ.app U (A.mul.app U (tensorSections A.carrier A.carrier U a b))) =
        (show Γ(T, g ⁻¹ᵁ U) from φ.app U a) * (show Γ(T, g ⁻¹ᵁ U) from φ.app U b)) :
    A.mul ≫ φ = (φ ⊗ₘ φ) ≫ pushforwardUnitMul g := by
  apply tensorObj_hom_ext
  intro U a b
  exact (hφ U a b).trans (tensorHom_pushforwardUnitMul_val_app_tensorSections A g φ U a b).symm

/-- Morphism-level multiplicativity ⇒ section-level. -/
theorem isAlgebraMap_mul_of_mul_comp (h : A.mul ≫ φ = (φ ⊗ₘ φ) ≫ pushforwardUnitMul g) :
    ∀ (U : X.Opens) (a b : A.carrier.val.obj (Opposite.op U)),
      (show Γ(T, g ⁻¹ᵁ U) from φ.app U (A.mul.app U (tensorSections A.carrier A.carrier U a b))) =
        (show Γ(T, g ⁻¹ᵁ U) from φ.app U a) * (show Γ(T, g ⁻¹ᵁ U) from φ.app U b) := by
  intro U a b
  have h' : (A.mul ≫ φ).val.app (Opposite.op U) (tensorSections A.carrier A.carrier U a b) =
      ((φ ⊗ₘ φ) ≫ pushforwardUnitMul g).val.app (Opposite.op U)
        (tensorSections A.carrier A.carrier U a b) := by rw [h]
  exact h'.trans (tensorHom_pushforwardUnitMul_val_app_tensorSections A g φ U a b)

/-- The unit clauses of two algebra maps give `A.one ≫ φ₁ = A.one ≫ φ₂`. -/
theorem one_comp_eq_of_isAlgebraMap_one
    (φ₁ φ₂ : A.carrier ⟶ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    (h₁ : ∀ U : X.Opens, (show Γ(T, g ⁻¹ᵁ U) from φ₁.app U (A.one.app U (show Γ(X, U) from 1))) = 1)
    (h₂ : ∀ U : X.Opens, (show Γ(T, g ⁻¹ᵁ U) from φ₂.app U (A.one.app U (show Γ(X, U) from 1))) = 1) :
    A.one ≫ φ₁ = A.one ≫ φ₂ :=
  unit_hom_ext fun U => (h₁ U).trans (h₂ U).symm

end AlgebraicGeometry.Scheme.QCAlgebra

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- Adjoint transposition of the product of two functionals:
`(homEquiv a ⊗ₘ homEquiv b) ≫ pushforwardUnitMul g = homEquiv (δ ≫ (a ⊗ₘ b) ≫ (λ_ O_T).hom)`. -/
theorem tensorHom_homEquiv_pushforwardUnitMul (g : T ⟶ X) {M N : X.Modules}
    (a : (pullback g).obj M ⟶ 𝟙_ T.Modules) (b : (pullback g).obj N ⟶ 𝟙_ T.Modules) :
    ((pullbackPushforwardAdjunction g).homEquiv _ _ a ⊗ₘ
        (pullbackPushforwardAdjunction g).homEquiv _ _ b) ≫ pushforwardUnitMul g =
      (pullbackPushforwardAdjunction g).homEquiv _ _
        (pullbackTensorObjHom g M N ≫ (a ⊗ₘ b) ≫ (λ_ (𝟙_ T.Modules)).hom) := by
  let _ := pushforwardLaxMonoidal g
  rw [Adjunction.homEquiv_naturality_right, Functor.map_comp, homEquiv_pullbackTensorObjHom,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  unfold pushforwardUnitMul
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc,
    CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules

end
