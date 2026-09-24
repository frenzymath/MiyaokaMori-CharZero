import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackPow
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMulEvaluationLocal
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoEvaluationUnit
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationEpi
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameRankOne
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FrameTensorPowSection

/-! # Local form of the powers `Ψ_e(x^{⊗e})` of a twisted section

**Local form of the powers `Ψ_e(x^{⊗e})`** (a step of the local computation of coordinate power sections,
at the variable level): `S` a graded quasi-coherent algebra on `X`, `π : Proj_X S → X`, `Q` an `O_X`-module, `q : ℕ`,
`Ψ_e := twistPullbackPow S q Q e : (O(q) ⊗ π^*Q)^{⊗e} ⟶ O(qe) ⊗ π^*Q^{⊗e}` (the body of `splitTwistMul`). If a global
section `x` of `O(q) ⊗ π^*Q` restricts on `π⁻¹V` (`V` affine) to the pure tensor `evaluationLocal S q V c ⊗ η(ε)`
(`c ∈ Γ(V, S_q)`, `ε ∈ Γ(V, Q)`, `η = unitSec` the adjunction unit), then for every `e` and every `w ∈ Γ(V, S_{qe})`
with `of (qe) w = (of q c)^e` in the section ring `A(V)`,
`Ψ_e(x^{⊗e})|_{π⁻¹V} = evaluationLocal S (qe) V w ⊗ η(ε^{⊗e})` (`ε^{⊗e} = framePow ε e`).

Proof: induction on `e` (see the docstring of the theorem). The inductive step is the multiplicativity of the evaluation
w.r.t. `twistMul` (`twistMul_app_moduleTensorSection_evaluationLocal`, `TwistMulEvaluationLocal`) together with the
pure-tensor formulas for `tensorMapHom`, `twistPullbackMul` (via `tensorμ`) and `pullbackTensorIso⁻¹` on unit sections,
all proved here.

Sources: Stacks 01MO, 01CD; the proof of Proposition 2.4 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- Composition on sections, elementwise (definitional). -/
theorem comp_app_apply_tppl {A B C : Y.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : Y.Opens) (x : Γ(A, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) := rfl

/-- `f.hom.app U x = y ⇒ f.inv.app U y = x`. -/
theorem iso_inv_app_eq_tppl {A B : Y.Modules} (f : A ≅ B) (U : Y.Opens) {x : Γ(A, U)} {y : Γ(B, U)}
    (h : f.hom.app U x = y) : f.inv.app U y = x := by
  subst h
  exact congrArg (fun k : A ⟶ A => k.app U x) f.hom_inv_id

/-- Right whisker on section pairs (public copy of `TwistPowerIsoSectionsGeneration.whiskerRight_app_tensorSections`). -/
theorem whiskerRight_app_tensorSections_tppl {A A' B : Y.Modules} (f : A ⟶ A') (U : Y.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 B) U a b

/-- Inverse associator on section pairs. -/
theorem associator_inv_app_tensorSections_tppl (A B C : Y.Modules) (U : Y.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    (α_ A B C).inv.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A (B ⊗ C) U a
        (AlgebraicGeometry.Scheme.Modules.tensorSections B C U b c)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (A ⊗ B) C U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) c :=
  iso_inv_app_eq_tppl (α_ A B C) U (associator_app_tensorSections A B C U a b c)

/-- **`tensorμ` on section pairs**: `(x₁ ⊗ x₂) ⊗ (y₁ ⊗ y₂) ↦ (x₁ ⊗ y₁) ⊗ (x₂ ⊗ y₂)`. -/
theorem tensorμ_app_tensorSections (X₁ X₂ Y₁ Y₂ : Y.Modules) (U : Y.Opens)
    (x₁ : Γ(X₁, U)) (x₂ : Γ(X₂, U)) (y₁ : Γ(Y₁, U)) (y₂ : Γ(Y₂, U)) :
    (CategoryTheory.MonoidalCategory.tensorμ X₁ X₂ Y₁ Y₂).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) U
          (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ X₂ U x₁ x₂)
          (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ Y₂ U y₁ y₂)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) U
        (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ Y₁ U x₁ y₁)
        (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ Y₂ U x₂ y₂) := by
  have e1 : (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) U
        (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ X₂ U x₁ x₂)
        (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ Y₂ U y₁ y₂)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections X₁ (X₂ ⊗ (Y₁ ⊗ Y₂)) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ (Y₁ ⊗ Y₂) U x₂
          (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ Y₂ U y₁ y₂)) :=
    associator_app_tensorSections X₁ X₂ (Y₁ ⊗ Y₂) U x₁ x₂ _
  have e2 : (X₁ ◁ (α_ X₂ Y₁ Y₂).inv).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ (X₂ ⊗ (Y₁ ⊗ Y₂)) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ (Y₁ ⊗ Y₂) U x₂
          (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ Y₂ U y₁ y₂))) =
      AlgebraicGeometry.Scheme.Modules.tensorSections X₁ ((X₂ ⊗ Y₁) ⊗ Y₂) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections (X₂ ⊗ Y₁) Y₂ U
          (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ Y₁ U x₂ y₁) y₂) :=
    (whiskerLeft_app_tensorSections X₁ (α_ X₂ Y₁ Y₂).inv U x₁ _).trans
      (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.tensorSections X₁ ((X₂ ⊗ Y₁) ⊗ Y₂) U x₁ z)
        (associator_inv_app_tensorSections_tppl X₂ Y₁ Y₂ U x₂ y₁ y₂))
  have e3 : (X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ ((X₂ ⊗ Y₁) ⊗ Y₂) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections (X₂ ⊗ Y₁) Y₂ U
          (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ Y₁ U x₂ y₁) y₂)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections X₁ ((Y₁ ⊗ X₂) ⊗ Y₂) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections (Y₁ ⊗ X₂) Y₂ U
          (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ X₂ U y₁ x₂) y₂) :=
    (whiskerLeft_app_tensorSections X₁ ((β_ X₂ Y₁).hom ▷ Y₂) U x₁ _).trans
      (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.tensorSections X₁ ((Y₁ ⊗ X₂) ⊗ Y₂) U x₁ z)
        ((whiskerRight_app_tensorSections_tppl (β_ X₂ Y₁).hom U _ y₂).trans
          (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.tensorSections (Y₁ ⊗ X₂) Y₂ U z y₂)
            (braiding_app_tensorSections X₂ Y₁ U x₂ y₁))))
  have e4 : (X₁ ◁ (α_ Y₁ X₂ Y₂).hom).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ ((Y₁ ⊗ X₂) ⊗ Y₂) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections (Y₁ ⊗ X₂) Y₂ U
          (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ X₂ U y₁ x₂) y₂)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections X₁ (Y₁ ⊗ (X₂ ⊗ Y₂)) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ (X₂ ⊗ Y₂) U y₁
          (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ Y₂ U x₂ y₂)) :=
    (whiskerLeft_app_tensorSections X₁ (α_ Y₁ X₂ Y₂).hom U x₁ _).trans
      (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.tensorSections X₁ (Y₁ ⊗ (X₂ ⊗ Y₂)) U x₁ z)
        (associator_app_tensorSections Y₁ X₂ Y₂ U y₁ x₂ y₂))
  have e5 : (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ (Y₁ ⊗ (X₂ ⊗ Y₂)) U x₁
        (AlgebraicGeometry.Scheme.Modules.tensorSections Y₁ (X₂ ⊗ Y₂) U y₁
          (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ Y₂ U x₂ y₂))) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) U
        (AlgebraicGeometry.Scheme.Modules.tensorSections X₁ Y₁ U x₁ y₁)
        (AlgebraicGeometry.Scheme.Modules.tensorSections X₂ Y₂ U x₂ y₂) :=
    associator_inv_app_tensorSections_tppl X₁ Y₁ (X₂ ⊗ Y₂) U x₁ y₁ _
  unfold CategoryTheory.MonoidalCategory.tensorμ
  exact (congrArg (fun z => (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv.app U ((X₁ ◁ (α_ Y₁ X₂ Y₂).hom).app U
      ((X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂).app U ((X₁ ◁ (α_ X₂ Y₁ Y₂).inv).app U z)))) e1).trans
    ((congrArg (fun z => (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv.app U ((X₁ ◁ (α_ Y₁ X₂ Y₂).hom).app U
      ((X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂).app U z))) e2).trans
    ((congrArg (fun z => (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv.app U ((X₁ ◁ (α_ Y₁ X₂ Y₂).hom).app U z)) e3).trans
    ((congrArg (fun z => (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv.app U z) e4).trans e5)))

/-- `tensorIsoTensorObj.hom` on a pure tensor (definitional). -/
theorem tensorIsoTensorObj_hom_app_moduleTensorSection_tppl (A B : Y.Modules) (U : Y.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b := rfl

/-- **`tensorMapHom f g` on a pure tensor over any open**. -/
theorem tensorMapHom_app_moduleTensorSection {A A' B B' : Y.Modules} (f : A ⟶ A') (g : B ⟶ B') (U : Y.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorMapHom f g).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (f.app U a) (g.app U b) := by
  have e1 : (f ⊗ₘ g).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B' U (f.app U a) (g.app U b) :=
    AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f g U a b
  have e2 : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A' B').inv.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections A' B' U (f.app U a) (g.app U b)) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (f.app U a) (g.app U b) :=
    tensorIsoTensorObj_inv_app_tensorSections A' B' U _ _
  unfold AlgebraicGeometry.Scheme.Modules.tensorMapHom
  exact (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A' B').inv.app U z) e1).trans e2

/-- The identity morphism acts as the identity on sections. -/
theorem id_app_apply_tppl (A : Y.Modules) (U : Y.Opens) (a : Γ(A, U)) : (𝟙 A : A ⟶ A).app U a = a := rfl

/-- Naturality of the unit section: `f^*φ (η_M x) = η_N (φ x)` (`pullback_map_app_unit_app` for `unitSec`). -/
theorem unitSec_map {X : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (x : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U) (MiyaokaMori.DualPullback.unitSec f M x) =
      MiyaokaMori.DualPullback.unitSec f N (φ.app U x) :=
  pullback_map_app_unit_app f φ U x

/-- `pullbackTensorObjHom` on the unit section of a section pair (`pullbackTensorObjHom_app_unit_tensorSections`). -/
theorem pullbackTensorObjHom_app_unitSec_tensorSections {X : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N).app (f ⁻¹ᵁ U)
        (MiyaokaMori.DualPullback.unitSec f (M ⊗ N) (AlgebraicGeometry.Scheme.Modules.tensorSections M N U m n)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (f ⁻¹ᵁ U)
        (MiyaokaMori.DualPullback.unitSec f M m) (MiyaokaMori.DualPullback.unitSec f N n) :=
  pullbackTensorObjHom_app_unit_tensorSections f M N U m n

/-- **`pullbackTensorIso⁻¹` on unit sections**: `η_M(m) ⊗ η_N(n) ↦ η_{M ⊗ N}(m ⊗ n)`. -/
theorem pullbackTensorIso_inv_app_moduleTensorSection_unitSec {X : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso f M N).inv.app (f ⁻¹ᵁ U)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (MiyaokaMori.DualPullback.unitSec f M m)
          (MiyaokaMori.DualPullback.unitSec f N n)) =
      MiyaokaMori.DualPullback.unitSec f (AlgebraicGeometry.Scheme.Modules.tensor M N)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m n) := by
  refine iso_inv_app_eq_tppl _ _ ?_
  have e1 : ((AlgebraicGeometry.Scheme.Modules.pullback f).map
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).hom).app (f ⁻¹ᵁ U)
        (MiyaokaMori.DualPullback.unitSec f (AlgebraicGeometry.Scheme.Modules.tensor M N)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m n)) =
      MiyaokaMori.DualPullback.unitSec f (M ⊗ N) (AlgebraicGeometry.Scheme.Modules.tensorSections M N U m n) :=
    unitSec_map f (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).hom U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m n)
  have e2 := pullbackTensorObjHom_app_unitSec_tensorSections f M N U m n
  have e3 := tensorIsoTensorObj_inv_app_tensorSections ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
    (MiyaokaMori.DualPullback.unitSec f M m) (MiyaokaMori.DualPullback.unitSec f N n)
  exact (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app (f ⁻¹ᵁ U)
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N).app (f ⁻¹ᵁ U) z)) e1).trans
    ((congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app (f ⁻¹ᵁ U) z) e2).trans e3)

/-- Restriction of `1`. -/
theorem res_one_tppl {W' W : Y.Opens} (h : W' ≤ W) :
    AlgebraicGeometry.Scheme.Modules.res (SheafOfModules.unit Y.ringCatSheaf) h (1 : Γ(Y, W)) = (1 : Γ(Y, W')) :=
  map_one (Y.presheaf.map (homOfLE h).op).hom

/-- `(λ_ A).inv a = 1 ⊗ a` on sections. -/
theorem leftUnitor_inv_app_tensorSections_tppl (A : Y.Modules) (U : Y.Opens) (a : Γ(A, U)) :
    (λ_ A).inv.app U a =
      AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) A U (1 : Γ(Y, U)) a :=
  iso_inv_app_eq_tppl (λ_ A) U ((leftUnitor_app_tensorSections A U 1 a).trans (one_smul _ a))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)


/-- Index transport of `evaluationLocal` along `m = n` (`subst`). -/
theorem eqToHom_app_evaluationLocal {m n : ℕ} (h : m = n) (V : X.affineOpens) (x : Γ(S.part m, V.1)) :
    (CategoryTheory.eqToHom (congrArg (fun k : ℕ => AlgebraicGeometry.Scheme.relativeProj.twist S (k : ℤ)) h)).app
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n V
        ((CategoryTheory.eqToHom (congrArg S.part h)).app V.1 x) := by
  subst h
  rfl

/-- `of n ((eqToHom h) x) = of m x` in the section ring (`mk_eqToHom_app`). -/
theorem sectionsOf_eqToHom_app {m n : ℕ} (h : m = n) (V : X.Opens) (x : Γ(S.part m, V)) :
    ((S.sectionsOf V n ((CategoryTheory.eqToHom (congrArg S.part h)).app V x) : S.sectionsGrading V n) :
        S.sectionsRing V) =
      ((S.sectionsOf V m x : S.sectionsGrading V m) : S.sectionsRing V) := by
  subst h
  rfl


set_option maxRecDepth 8192 in
/-- **`twistPullbackMul` on pure tensors**: `(s ⊗ m) ⊗ (t ⊗ n) ↦ twistMul(s ⊗ t) ⊗ pullbackTensorIso⁻¹(m ⊗ n)`
(`tensorμ` reorders the factors, `tensorμ_app_tensorSections`). -/
theorem twistPullbackMul_app_moduleTensorSection (a b : ℤ) (M N : X.Modules)
    (U : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (s : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, U))
    (m : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj M, U))
    (t : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, U))
    (n : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj N, U)) :
    (twistPullbackMul S a b M N).app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s m) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t n)) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t))
        ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv.app
          U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m n)) := by
  have e2 : ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ⊗ₘ
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s m) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t n)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U s m)
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U t n) :=
    AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections _ _ U _ _
  have e3 := AlgebraicGeometry.Scheme.Modules.tensorμ_app_tensorSections
    (AlgebraicGeometry.Scheme.relativeProj.twist S a)
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj M)
    (AlgebraicGeometry.Scheme.relativeProj.twist S b)
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj N) U s m t n
  have e4 : (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S a b) ⊗ₘ
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
          (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv)).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U s t)
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U m n)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t))
        ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv.app
          U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m n)) := by
    refine (AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections _ _ U _ _).trans ?_
    refine congrArg₂ (fun z₁ z₂ => AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U z₁ z₂) ?_ ?_
    · exact congrArg (fun z => (AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app U z)
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections _ _ U s t)
    · exact congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
        (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv.app U z)
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections _ _ U m n)
  have e5 := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections
    (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
      (AlgebraicGeometry.Scheme.Modules.tensor M N)) U
    ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t))
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv.app
      U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m n))
  unfold twistPullbackMul
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app U
    ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S a b) ⊗ₘ
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
          (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv)).app U
      ((CategoryTheory.MonoidalCategory.tensorμ (AlgebraicGeometry.Scheme.relativeProj.twist S a)
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj M)
        (AlgebraicGeometry.Scheme.relativeProj.twist S b)
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj N)).app U z)))
      e2).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app U
    ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S a b) ⊗ₘ
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
          (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv)).app U z)) e3).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app U z) e4).trans ?_
  exact e5

set_option maxRecDepth 8192 in
/-- **Local form of the powers `Ψ_e(x^{⊗e})`**. `Ψ_e = twistPullbackPow S q Q e`. If the global section
`x` of `O(q) ⊗ π^*Q` restricts on `π⁻¹V` (`V` affine) to `evaluationLocal S q V c ⊗ η(ε)`, then for every `e` and every
`w ∈ Γ(V, S_{qe})` with `of (qe) w = (of q c)^e` in `A(V)`,
`Ψ_e(x^{⊗e})|_{π⁻¹V} = evaluationLocal S (qe) V w ⊗ η(framePow ε e)`.

Proof by induction on `e`.
* `e = 0`: `x^{⊗0} = 1`, `Ψ_0 = λ⁻¹ ≫ (twistUnitSection ⊗ pullbackUnitIso⁻¹) ≫ τ⁻¹` (`twistPullbackPow_zero`), so
  `Ψ_0(1)|_{π⁻¹V} = twistUnitSection(1) ⊗ pullbackUnitIso⁻¹(1) = evaluationLocal S 0 V (S.one 1) ⊗ η(1)`
  (`leftUnitor_inv_app_tensorSections`, `tensorHom_tensorSections`, `twistUnitSection_app_one`,
  `pullbackUnitIso_inv_app_app`); `of 0 (S.one 1) = 1 = (of q c)^0 = of 0 w` forces `w = S.one 1`
  (`sectionsOf_one_app_one`, `DirectSum.of_injective`).
* `e + 1`: `x^{⊗(e+1)} = x^{⊗e} ⊗ x` and `Ψ_{e+1} = (Ψ_e ⊗ 𝟙) ≫ twistPullbackMul ≫ (eqToHom ⊗ 𝟙)`
  (`twistPullbackPow_succ`). Restricting to `π⁻¹V` (`Hom.app_res`, `moduleTensorSection_restrict`) and using the
  induction hypothesis for the `w_e` with `of (qe) w_e = (of q c)^e` (`SetLike.pow_mem_graded`) and `hx`,
  `Ψ_{e+1}(x^{⊗(e+1)})|_{π⁻¹V} = (eqToHom ⊗ 𝟙)(twistPullbackMul((ev w_e ⊗ η ε^{⊗e}) ⊗ (ev c ⊗ η ε)))`
  `= (eqToHom (twistMul (ev w_e ⊗ ev c))) ⊗ pullbackTensorIso⁻¹(η ε^{⊗e} ⊗ η ε)` (`tensorMapHom_app_moduleTensorSection`,
  `twistPullbackMul_app_moduleTensorSection`) `= ev (q(e+1)) (eqToHom (w_e · c)) ⊗ η(ε^{⊗(e+1)})`
  (`twistMul_app_moduleTensorSection_evaluationLocal` — the multiplicativity of the evaluation —
  `eqToHom_app_evaluationLocal`, `pullbackTensorIso_inv_app_moduleTensorSection_unitSec`), and
  `of (q(e+1)) (eqToHom (w_e · c)) = of (qe) w_e · of q c = (of q c)^{e+1} = of (q(e+1)) w` gives
  `w = eqToHom (w_e · c)` (`sectionsOf_eqToHom_app`, `sectionsOf_sectionsGMul`, `DirectSum.of_injective`).

Edge cases: `e = 0` is the base case (`Q^{⊗0} = O`, `η(1) = 1`); `V = ⊥` trivial; `q = 0` allowed. -/
theorem twistPullbackPow_app_res_tensorPowSection (q : ℕ) (Q : X.Modules) (V : X.affineOpens)
    (x : Γ(AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q), ⊤))
    (c : Γ(S.part q, V.1)) (ε : Γ(Q, V.1))
    (hx : AlgebraicGeometry.Scheme.Modules.res
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q))
        le_top x =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S q V c)
        (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom Q ε))
    (e : ℕ) (w : Γ(S.part (q * e), V.1))
    (hw : ((S.sectionsOf V.1 (q * e) w : S.sectionsGrading V.1 (q * e)) : S.sectionsRing V.1) =
      ((S.sectionsOf V.1 q c : S.sectionsGrading V.1 q) : S.sectionsRing V.1) ^ e) :
    AlgebraicGeometry.Scheme.Modules.res
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)))
        le_top ((twistPullbackPow S q Q e).app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection x e)) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S (q * e) V w)
        (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) (AlgebraicGeometry.Scheme.Modules.framePow ε e)) := by
  induction e with
  | zero =>
    -- `w = S.one 1`
    have hw1 : DirectSum.of (S.sectionsPiece V.1) (q * 0) w =
        DirectSum.of (S.sectionsPiece V.1) (q * 0) (S.one.app V.1 (1 : Γ(X, V.1))) := by
      refine (hw.trans ?_).trans (sectionsOf_one_app_one S V.1).symm
      exact pow_zero _
    have hw' : w = S.one.app V.1 (1 : Γ(X, V.1)) := DirectSum.of_injective (q * 0) hw1
    subst hw'
    -- restriction of `1`
    have r1 : AlgebraicGeometry.Scheme.Modules.res
        (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) 0)
        (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection x 0) =
        (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) :=
      AlgebraicGeometry.Scheme.Modules.res_one_tppl _
    have hres := (AlgebraicGeometry.Scheme.Modules.Hom.app_res (twistPullbackPow S q Q 0)
      (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection x 0)).symm
    rw [hres, r1]
    -- the three factors
    have h0 : (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left,
        (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) =
        (AlgebraicGeometry.Scheme.relativeProj S).hom.app V.1 (1 : Γ(X, V.1)) :=
      (map_one ((AlgebraicGeometry.Scheme.relativeProj S).hom.app V.1).hom).symm
    have hpu : (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) =
        MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
          (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, V.1)) :=
      (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app _ z) h0).trans
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_inv_app_app _ V.1 1)
    have hl := AlgebraicGeometry.Scheme.Modules.leftUnitor_inv_app_tensorSections_tppl
      (𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules) ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))
    have ht := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (twistUnitSection S)
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))
      (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))
    have hu := twistUnitSection_app_one S V
    have hτ := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections
      (AlgebraicGeometry.Scheme.relativeProj.twist S 0)
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (SheafOfModules.unit X.ringCatSheaf))
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 V (S.one.app V.1 (1 : Γ(X, V.1))))
      (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
          (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, V.1)))
    rw [twistPullbackPow_zero]
    refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app _
      ((twistUnitSection S ⊗ₘ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (AlgebraicGeometry.Scheme.relativeProj S).hom).inv).app _ z)) hl).trans ?_
    refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app _ z) ht).trans ?_
    refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app _
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ _ z _)) hu).trans ?_
    refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app _
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ _ _ z)) hpu).trans ?_
    exact hτ
  | succ e ih =>
    -- `w₀ ∈ Γ(V, S_{qe})` with `of (qe) w₀ = (of q c)^e`
    have hcmem : ((S.sectionsOf V.1 q c : S.sectionsGrading V.1 q) : S.sectionsRing V.1) ∈
        S.sectionsGrading V.1 q := (S.sectionsOf V.1 q c).2
    have hpow := SetLike.pow_mem_graded e hcmem
    have hidx : e • q = q * e := by rw [smul_eq_mul, mul_comm]
    rw [hidx] at hpow
    obtain ⟨w₀, hw₀⟩ := AddMonoidHom.mem_range.mp hpow
    have hw₀' : ((S.sectionsOf V.1 (q * e) w₀ : S.sectionsGrading V.1 (q * e)) : S.sectionsRing V.1) =
        ((S.sectionsOf V.1 q c : S.sectionsGrading V.1 q) : S.sectionsRing V.1) ^ e := hw₀
    have IH := ih w₀ hw₀'
    -- identify `w` as the transported product `w₀ · c`
    have hn : q * e + q = q * (e + 1) := by ring
    have hw1 : DirectSum.of (S.sectionsPiece V.1) (q * (e + 1)) w =
        DirectSum.of (S.sectionsPiece V.1) (q * (e + 1))
          ((CategoryTheory.eqToHom (congrArg S.part hn)).app V.1 (S.sectionsGMul V.1 w₀ c)) := by
      refine hw.trans ?_
      rw [pow_succ, ← hw₀']
      exact (sectionsOf_sectionsGMul S V.1 w₀ c).symm.trans (sectionsOf_eqToHom_app S hn V.1 _).symm
    have hw' : w = (CategoryTheory.eqToHom (congrArg S.part hn)).app V.1 (S.sectionsGMul V.1 w₀ c) :=
      DirectSum.of_injective (β := S.sectionsPiece V.1) (q * (e + 1)) hw1
    subst hw'
    -- notation-free bookkeeping
    have hres := (AlgebraicGeometry.Scheme.Modules.Hom.app_res (twistPullbackPow S q Q (e + 1))
      (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection x (e + 1))).symm
    have hB : AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) (e + 1))
        (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection x (e + 1)) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          (AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e)
            (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤)
            (AlgebraicGeometry.Scheme.Modules.tensorPowSection x e))
          (AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q))
            (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤) x) :=
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (CategoryTheory.homOfLE le_top)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection x e) x
    have hC : (twistPullbackPow S q Q e).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        (AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e)
          (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤)
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection x e)) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S (q * e) V w₀)
          (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) (AlgebraicGeometry.Scheme.Modules.framePow ε e)) :=
      (AlgebraicGeometry.Scheme.Modules.Hom.app_res (twistPullbackPow S q Q e) le_top _).trans IH
    have hD := AlgebraicGeometry.Scheme.Modules.tensorMapHom_app_moduleTensorSection (twistPullbackPow S q Q e)
      (𝟙 _) ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      (AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e)
        (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection x e))
      (AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q))
        (le_top : (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤ ⊤) x)
    rw [hC, AlgebraicGeometry.Scheme.Modules.id_app_apply_tppl, hx] at hD
    have hE := twistPullbackMul_app_moduleTensorSection S ((q * e : ℕ) : ℤ) (q : ℤ)
      (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S (q * e) V w₀)
      (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
        (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) (AlgebraicGeometry.Scheme.Modules.framePow ε e))
      (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S q V c)
      (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom Q ε)
    have hF := AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_inv_app_moduleTensorSection_unitSec
      (AlgebraicGeometry.Scheme.relativeProj S).hom (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q V.1
      (AlgebraicGeometry.Scheme.Modules.framePow ε e) ε
    rw [hF] at hE
    -- the `eqToHom` index transport, split into the two transports
    have h₁ : AlgebraicGeometry.Scheme.relativeProj.twist S (((q * e : ℕ) : ℤ) + (q : ℤ)) =
        AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e + q : ℕ) : ℤ) :=
      congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (Nat.cast_add (q * e) q).symm
    have h₂ : AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e + q : ℕ) : ℤ) =
        AlgebraicGeometry.Scheme.relativeProj.twist S ((q * (e + 1) : ℕ) : ℤ) :=
      congrArg (fun k : ℕ => AlgebraicGeometry.Scheme.relativeProj.twist S (k : ℤ)) hn
    have hsplit : (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S)
        (show ((q * e : ℕ) : ℤ) + (q : ℤ) = ((q * (e + 1) : ℕ) : ℤ) by push_cast; ring)) :
          AlgebraicGeometry.Scheme.relativeProj.twist S (((q * e : ℕ) : ℤ) + (q : ℤ)) ⟶
            AlgebraicGeometry.Scheme.relativeProj.twist S ((q * (e + 1) : ℕ) : ℤ)) =
        CategoryTheory.eqToHom h₁ ≫ CategoryTheory.eqToHom h₂ :=
      (CategoryTheory.eqToHom_trans h₁ h₂).symm
    have hG := AlgebraicGeometry.Scheme.Modules.tensorMapHom_app_moduleTensorSection
      (CategoryTheory.eqToHom h₁ ≫ CategoryTheory.eqToHom h₂) (𝟙 _)
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      ((AlgebraicGeometry.Scheme.relativeProj.twistMul S ((q * e : ℕ) : ℤ) (q : ℤ)).app _
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S (q * e) V w₀)
          (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S q V c)))
      (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.Modules.framePow ε e) ε))
    rw [AlgebraicGeometry.Scheme.Modules.id_app_apply_tppl] at hG
    have hH : (CategoryTheory.eqToHom h₁ ≫ CategoryTheory.eqToHom h₂).app _
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S ((q * e : ℕ) : ℤ) (q : ℤ)).app _
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S (q * e) V w₀)
            (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S q V c))) =
        AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S (q * (e + 1)) V
          ((CategoryTheory.eqToHom (congrArg S.part hn)).app V.1 (S.sectionsGMul V.1 w₀ c)) := by
      refine (congrArg (fun z => (CategoryTheory.eqToHom h₂).app _ z)
        (AlgebraicGeometry.Scheme.relativeProj.twistMul_app_moduleTensorSection_evaluationLocal S (q * e) q V w₀ c)).trans ?_
      exact eqToHom_app_evaluationLocal S hn V _
    -- assemble
    rw [hres, hB, twistPullbackPow_succ, hsplit, hx]
    refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorMapHom
      (CategoryTheory.eqToHom h₁ ≫ CategoryTheory.eqToHom h₂) (𝟙 _)).app _
      ((twistPullbackMul S ((q * e : ℕ) : ℤ) (q : ℤ) (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q).app _ z))
      hD).trans ?_
    refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorMapHom
      (CategoryTheory.eqToHom h₁ ≫ CategoryTheory.eqToHom h₂) (𝟙 _)).app _ z) hE).trans ?_
    refine hG.trans ?_
    exact congrArg (fun z => AlgebraicGeometry.Scheme.Modules.moduleTensorSection z
      (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.Modules.framePow ε e) ε))) hH

/-- `twistPullbackPow_app_res_tensorPowSection` followed by the index transport `qk = m` (the shape of `splitTwistMul`
after `splitTwistMul_eq_twistPullbackPow`): with `w ∈ Γ(V, S_m)`, `of m w = (of q c)^k`,
`((Ψ_k ≫ eqToHom h) (x^{⊗k}))|_{π⁻¹V} = evaluationLocal S m V w ⊗ η(framePow ε k)`. The object equation `h` is an explicit
argument (any proof; in the application it is `splitTwistMul_index_eq`, so that the concrete instance is syntactically the
term produced by `splitTwistMul_eq_twistPullbackPow`; the kernel would otherwise unfold both sides).
Proof: `subst` the index equation, `eqToHom_refl`, and `twistPullbackPow_app_res_tensorPowSection`. -/
theorem twistPullbackPow_comp_eqToHom_app_res_tensorPowSection (q : ℕ) (Q : X.Modules) (V : X.affineOpens)
    (x : Γ(AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q), ⊤))
    (c : Γ(S.part q, V.1)) (ε : Γ(Q, V.1))
    (hx : AlgebraicGeometry.Scheme.Modules.res
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q))
        le_top x =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S q V c)
        (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom Q ε))
    (k m : ℕ) (hkq : q * k = m) (w : Γ(S.part m, V.1))
    (hw : ((S.sectionsOf V.1 m w : S.sectionsGrading V.1 m) : S.sectionsRing V.1) =
      ((S.sectionsOf V.1 q c : S.sectionsGrading V.1 q) : S.sectionsRing V.1) ^ k)
    (h : AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * k : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q k)) =
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q k))) :
    AlgebraicGeometry.Scheme.Modules.res
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q k)))
        le_top
        (((twistPullbackPow S q Q k ≫ CategoryTheory.eqToHom h).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection x k)) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V w)
        (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q k) (AlgebraicGeometry.Scheme.Modules.framePow ε k)) := by
  subst hkq
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.Category.comp_id]
  exact twistPullbackPow_app_res_tensorPowSection S q Q V x c ε hx k w hw
end AlgebraicGeometry.Scheme.relativeProj

end
