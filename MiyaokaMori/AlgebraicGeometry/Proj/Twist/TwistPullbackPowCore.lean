import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionRing
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulUnitRight
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoEvaluationUnit
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationEpi

/-! # `twistPullbackPow`: core definitions

Definitions and elementary lemmas for the variable-level body `Ψ = twistPullbackPow` of `splitTwistMul` (kept in
their own module so that the single-file compile time of the block multiplicativity proof stays small):

* `tensorMapHom`, `tensorPowSplitHom` and their section-level formulas (the section formula of `tensorPowAddIso`
  is `tensorPowAddIso_app_top_tensorPowSection`, `TensorPowIsoSection`);
* `twistUnitSection S : 𝟙_ ⟶ O(0)`, `twistPullbackMul`, `twistPullbackPow`, `twistPullbackPowMul` and the
  definitional recursion lemmas `twistPullbackPow_zero`, `twistPullbackPow_succ(_def)`;
* `twistMul_unit_right` (Stacks 01MO): the right unit law of `twistMul`, the only non-coherence input of the block
  multiplicativity, proved as the instance `u := twistUnitSection S` of `twistMul_unit_right_of_app_one`
  (`TwistMulUnitRight`, via the chart projections), using `twistUnitSection_app_one` (the unit section over
  `π⁻¹U` is `evaluationLocal S 0 U (S.one 1)`);
* `IsIso` facts as theorems with file-local `attribute [local instance]` (no global instance).

Sources: Stacks 01MO/01MS/01CD; the proof of Proposition 2.4 of the paper. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- Functoriality of `Modules.tensor`, transported from the monoidal `⊗ₘ` through `tensorIsoTensorObj`. -/
noncomputable def tensorMapHom {A A' B B' : Y.Modules} (f : A ⟶ A') (g : B ⟶ B') :
    AlgebraicGeometry.Scheme.Modules.tensor A B ⟶ AlgebraicGeometry.Scheme.Modules.tensor A' B' :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom ≫ (f ⊗ₘ g) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A' B').inv

/-- `L^{⊗(e+e')} ⟶ L^{⊗e} ⊗ L^{⊗e'}` (as `Modules.tensor`): `tensorPowAddIso` followed by `tensorIsoTensorObj⁻¹`. -/
noncomputable def tensorPowSplitHom (L : Y.Modules) (e e' : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPow L (e + e') ⟶
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L e)
        (AlgebraicGeometry.Scheme.Modules.tensorPow L e') :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L e e').hom ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv

theorem tensorMapHom_isIso {A A' B B' : Y.Modules} (f : A ⟶ A') (g : B ⟶ B') [IsIso f] [IsIso g] :
    IsIso (tensorMapHom f g) := by
  unfold tensorMapHom; infer_instance

theorem tensorPowSplitHom_isIso (L : Y.Modules) (e e' : ℕ) : IsIso (tensorPowSplitHom L e e') := by
  unfold tensorPowSplitHom; infer_instance

/- `IsIso` facts are theorems; the instance attribute is file-local and does not reach importers. -/
attribute [local instance] tensorMapHom_isIso tensorPowSplitHom_isIso


/-- Composition on sections, elementwise (definitional). -/
theorem comp_app_apply_stma {A B C : Y.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : Y.Opens)
    (x : (A.val.obj (Opposite.op U) : Type u)) : (f ≫ g).app U x = g.app U (f.app U x) := rfl

/-- Congruence at the section level for `f ≫ eqToHom h`, morphisms as variables (a bridge lemma: the concrete instance
is syntactically the goal, so the kernel does not unfold the concrete morphisms). -/
theorem comp_eqToHom_app_top_apply_congr {A B B' : Y.Modules} (f g : A ⟶ B) (hfg : f = g) (h : B = B')
    (x : (A.val.obj (Opposite.op ⊤) : Type u)) :
    ((f ≫ CategoryTheory.eqToHom h).val.app (Opposite.op ⊤)).hom x =
      ((g ≫ CategoryTheory.eqToHom h).val.app (Opposite.op ⊤)).hom x := by
  subst hfg; rfl

/-- `tensorIsoTensorObj.inv` on a pure tensor `tensorSections a b` is `sectionTensor a b`. -/
theorem tensorIsoTensorObj_inv_app_top_tensorSections {A B : Y.Modules}
    (a : (A.val.obj (Opposite.op ⊤) : Type u)) (b : (B.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).inv.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B ⊤ a b) = sectionTensor a b := by
  have h := congrArg (fun φ => φ.app ⊤ (sectionTensor a b))
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom_inv_id
  exact h

/-- `tensorIsoTensorObj.hom` on a pure tensor `sectionTensor a b` is `tensorSections a b` (definitional). -/
theorem tensorIsoTensorObj_hom_app_top_sectionTensor {A B : Y.Modules}
    (a : (A.val.obj (Opposite.op ⊤) : Type u)) (b : (B.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom.app ⊤ (sectionTensor a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B ⊤ a b := rfl

/-- `tensorMapHom f g` on a pure tensor. -/
theorem tensorMapHom_app_top_sectionTensor {A A' B B' : Y.Modules} (f : A ⟶ A') (g : B ⟶ B')
    (a : (A.val.obj (Opposite.op ⊤) : Type u)) (b : (B.val.obj (Opposite.op ⊤) : Type u)) :
    (tensorMapHom f g).app ⊤ (sectionTensor a b) = sectionTensor (f.app ⊤ a) (g.app ⊤ b) := by
  change (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A' B').inv.app ⊤
    ((f ⊗ₘ g).val.app (Opposite.op ⊤)
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom.app ⊤ (sectionTensor a b))) = _
  rw [tensorIsoTensorObj_hom_app_top_sectionTensor, AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
  exact tensorIsoTensorObj_inv_app_top_tensorSections _ _

/-- **`tensorPowAddIso` on a pure tensor power**:
`(tensorPowAddIso L e e').hom` sends `s^{⊗(e+e')}` to `s^{⊗e} ⊗ s^{⊗e'}`.

**Natural-language proof** (by induction on `e'`; `tensorPowAddIso` is defined by recursion on `e'`,
`LineBundleSectionRing`):
* `e' = 0`: `tensorPowAddIso L e 0 = (ρ_ L^{⊗e}).symm ≪≫ whiskerLeftIso _ (eqToIso (𝟙_ = unit))` and
  `s^{⊗(e+0)} = s^{⊗e}` (definitional), `s^{⊗0} = 1`. By `rightUnitor_app_tensorSections`
  (`ModulesTensorSectionsCoherence`), `(ρ_ A).hom (tensorSections a 1) = 1 • a = a`, so `(ρ_ A).inv a = tensorSections a 1`;
  the whisker `A ◁ eqToHom _` acts on the second factor (`tensorHom_tensorSections` with `𝟙`) and `eqToHom` between
  `𝟙_` and `SheafOfModules.unit` (equal after `with_unfolding_all`) sends `1` to `1`.
* `e' + 1`: `tensorPowAddIso L e (e'+1) = tensorIsoTensorObj ≪≫ whiskerRightIso (tensorPowAddIso L e e') L ≪≫ α_ ≪≫
  whiskerLeftIso _ (tensorIsoTensorObj _ _).symm`, and `s^{⊗(e+e'+1)} = sectionTensor s^{⊗(e+e')} s` (definition of
  `tensorPowSection`). Apply `tensorIsoTensorObj_hom_app_top_sectionTensor` (gives `tensorSections s^{⊗(e+e')} s`),
  `whiskerRight_app_tensorSections` + the induction hypothesis (gives `tensorSections (tensorSections s^{⊗e} s^{⊗e'}) s`),
  `associator_app_tensorSections` (gives `tensorSections s^{⊗e} (tensorSections s^{⊗e'} s)`), then the whisker of
  `tensorIsoTensorObj.inv` on the second factor (`tensorIsoTensorObj_inv_app_top_tensorSections`) gives
  `tensorSections s^{⊗e} (sectionTensor s^{⊗e'} s) = tensorSections s^{⊗e} s^{⊗(e'+1)}`.

**Library facts used**: `rightUnitor_app_tensorSections`, `associator_app_tensorSections`
(`ModulesTensorSectionsCoherence`), `tensorHom_tensorSections`,
`whiskerRight_app_tensorSections` (`TwistPowerIsoSectionsGeneration`, re-derivable from `tensorHom_tensorSections`).

**Edge cases**: `e = 0` is included (`L^{⊗0} = unit`, `s^{⊗0} = 1`); `L` need not be a line bundle.

Estimated 60–100 lines, medium (the `𝟙_` vs `SheafOfModules.unit` `eqToHom` in the base case is the only delicate point). -/
theorem tensorPowAddIso_hom_app_top_tensorPowSection (L : Y.Modules) (s : (L.val.obj (Opposite.op ⊤) : Type u))
    (e e' : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L e e').hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (e + e')) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.tensorPow L e) (AlgebraicGeometry.Scheme.Modules.tensorPow L e') ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e') :=
  AlgebraicGeometry.Scheme.Modules.tensorPowAddIso_app_top_tensorPowSection L s e e'

/-- `tensorPowSplitHom` on a pure tensor power: `s^{⊗(e+e')} ↦ s^{⊗e} ⊗ s^{⊗e'}` (as `sectionTensor`). -/
theorem tensorPowSplitHom_app_top_tensorPowSection (L : Y.Modules) (s : (L.val.obj (Opposite.op ⊤) : Type u))
    (e e' : ℕ) :
    (tensorPowSplitHom L e e').app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (e + e')) =
      sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e') := by
  change (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv.app ⊤
    ((AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L e e').hom.app ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (e + e'))) = _
  rw [tensorPowAddIso_hom_app_top_tensorPowSection]
  exact tensorIsoTensorObj_inv_app_top_tensorSections _ _




end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/- File-local instance attributes (they expired with the previous namespace block). -/
attribute [local instance] AlgebraicGeometry.Scheme.Modules.tensorMapHom_isIso
  AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom_isIso

/-- `𝟙_ ⟶ O(0)`: the unit section `1` of the twisting sheaf (`1 ∈ S_0` evaluated on `Proj_X S`). -/
noncomputable def twistUnitSection :
    𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules ⟶ AlgebraicGeometry.Scheme.relativeProj.twist S 0 :=
  (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫
    AlgebraicGeometry.Scheme.relativeProj.evaluation S 0

/-- **The unit section over `π⁻¹V` is `evaluationLocal S 0 V (S.one 1)`**: `twistUnitSection S` on `1 ∈ Γ(π⁻¹V, O)`
is the local evaluation of the unit `S.one.app V 1 ∈ Γ(V, S_0)` (`pullbackUnitIso_inv_app_app`,
`pullback_map_app_unit_app`, `evaluation_app_unit`). Used by `TwistPullbackPowLocal`, which imports this module. -/
theorem twistUnitSection_app_one (V : X.affineOpens) :
    (twistUnitSection S).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 V (S.one.app V.1 (1 : Γ(X, V.1))) := by
  have h0 : (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left,
      (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) =
      (AlgebraicGeometry.Scheme.relativeProj S).hom.app V.1 (1 : Γ(X, V.1)) :=
    (map_one ((AlgebraicGeometry.Scheme.relativeProj S).hom.app V.1).hom).symm
  have h1 := AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_inv_app_app
    (AlgebraicGeometry.Scheme.relativeProj S).hom V.1 (1 : Γ(X, V.1))
  have h2 := AlgebraicGeometry.Scheme.Modules.pullback_map_app_unit_app
    (AlgebraicGeometry.Scheme.relativeProj S).hom S.one V.1 (1 : Γ(X, V.1))
  have h3 := AlgebraicGeometry.Scheme.relativeProj.evaluation_app_unit S 0 V (S.one.app V.1 (1 : Γ(X, V.1)))
  unfold twistUnitSection
  exact (congrArg (fun z => (AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app _
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one).app _
        ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app _ z)))
      h0).trans
    ((congrArg (fun z => (AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app _
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one).app _ z))
      h1).trans
    ((congrArg (fun z => (AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app _ z) h2).trans h3))

/-- `(O(a) ⊗ π^*M) ⊗ (O(b) ⊗ π^*N) ⟶ O(a+b) ⊗ π^*(M ⊗ N)` (all tensors `Modules.tensor`):
`tensorμ` reordering, then `twistMul S a b` on the twist factors and `pullbackTensorIso⁻¹` on the pullback factors. -/
noncomputable def twistPullbackMul (a b : ℤ) (M N : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S a)
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj M))
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S b)
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj N)) ⟶
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensor M N)) :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ⊗ₘ
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom) ≫
    CategoryTheory.MonoidalCategory.tensorμ _ _ _ _ ≫
    (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S a b) ⊗ₘ
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
          (AlgebraicGeometry.Scheme.relativeProj S).hom M N).inv)) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv

theorem tensorμ_isIso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (A B A' B' : C) :
    IsIso (CategoryTheory.MonoidalCategory.tensorμ A B A' B') := by
  unfold CategoryTheory.MonoidalCategory.tensorμ; infer_instance

/- Keyed on Mathlib's `tensorμ`: deliberately file-local, never a global instance. -/
attribute [local instance] tensorμ_isIso

theorem twistPullbackMul_isIso (a b : ℤ) (M N : X.Modules)
    [IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMul S a b)] :
    IsIso (twistPullbackMul S a b M N) := by
  unfold twistPullbackMul; infer_instance

attribute [local instance] twistPullbackMul_isIso  -- file-local

/-- Ψ_e : (O(q) ⊗ π^*Q)^{⊗e} ⟶ O(qe) ⊗ π^*(Q^{⊗e}), the body of `splitTwistMul` at the variable level
(same `Nat.rec` term; see `splitTwistMul_eq_twistPullbackPow`). -/
noncomputable def twistPullbackPow (q : ℕ) (Q : X.Modules) (e : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPow
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e ⟶
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)) :=
  let π := (AlgebraicGeometry.Scheme.relativeProj S).hom
  let T := AlgebraicGeometry.Scheme.relativeProj.twist S
  let τ := fun A B : (AlgebraicGeometry.Scheme.relativeProj S).left.Modules =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B
  Nat.rec (motive := fun e =>
      AlgebraicGeometry.Scheme.Modules.tensorPow
          (AlgebraicGeometry.Scheme.Modules.tensor (T (q : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)) e ⟶
        AlgebraicGeometry.Scheme.Modules.tensor (T ((q * e : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)))
    ((CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
        (SheafOfModules.unit _)).inv ≫
      CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
        ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso π).inv ≫
          (AlgebraicGeometry.Scheme.Modules.pullback π).map S.one ≫
          AlgebraicGeometry.Scheme.relativeProj.evaluation S 0)
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso π).inv ≫
      (τ _ _).inv)
    (fun e Ψe =>
      (τ _ _).hom ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
          (Ψe ≫ (τ _ _).hom) (τ _ _).hom ≫
        CategoryTheory.MonoidalCategory.tensorμ (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules) _ _ _ _ ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
          ((τ _ _).inv ≫ AlgebraicGeometry.Scheme.relativeProj.twistMul S _ _ ≫
            CategoryTheory.eqToHom (congrArg T (by push_cast; ring)))
          ((τ _ _).inv ≫ (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π _ _).inv) ≫
        (τ _ _).inv)
    e

/-- Ψ_0 is `1 ↦ 1 ⊗ 1` (definitional). -/
theorem twistPullbackPow_zero (q : ℕ) (Q : X.Modules) :
    twistPullbackPow S q Q 0 =
      (λ_ (𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)).inv ≫
        (twistUnitSection S ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv := rfl

/-- The recursion of Ψ, definitional form. -/
theorem twistPullbackPow_succ_def (q : ℕ) (Q : X.Modules) (e : ℕ) :
    twistPullbackPow S q Q (e + 1) =
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
        ((twistPullbackPow S q Q e ≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom) ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom) ≫
        CategoryTheory.MonoidalCategory.tensorμ _ _ _ _ ≫
        (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
            AlgebraicGeometry.Scheme.relativeProj.twistMul S ((q * e : ℕ) : ℤ) (q : ℤ) ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S)
              (by push_cast; ring))) ⊗ₘ
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
            (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (AlgebraicGeometry.Scheme.relativeProj S).hom
              (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q).inv)) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv := rfl

/-- The recursion of Ψ in terms of `twistPullbackMul`:
`Ψ_{e+1} = (Ψ_e ⊗ 𝟙) ≫ μ_{qe,q} ≫ (eqToHom ⊗ 𝟙)`. -/
theorem twistPullbackPow_succ (q : ℕ) (Q : X.Modules) (e : ℕ) :
    twistPullbackPow S q Q (e + 1) =
      AlgebraicGeometry.Scheme.Modules.tensorMapHom (twistPullbackPow S q Q e) (𝟙 _) ≫
        twistPullbackMul S ((q * e : ℕ) : ℤ) (q : ℤ) (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom
          (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S)
            (show ((q * e : ℕ) : ℤ) + (q : ℤ) = ((q * (e + 1) : ℕ) : ℤ) by push_cast; ring))) (𝟙 _) := by
  rw [twistPullbackPow_succ_def]
  unfold AlgebraicGeometry.Scheme.Modules.tensorMapHom twistPullbackMul
  simp only [Category.assoc, Iso.inv_hom_id_assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]
  rfl

/-- **Right unit law of `twistMul`** (Stacks 01MO):
`O(a) ⊗ 𝟙_ --(𝟙 ⊗ 1)--> O(a) ⊗ O(0) --twistMul--> O(a)` is the right unitor (up to the index transport `a + 0 = a`),
where `1 := twistUnitSection S : 𝟙_ ⟶ O(0)` is `1 ∈ S_0` evaluated on `Proj_X S`
(`pullbackUnitIso⁻¹ ≫ π^*(S.one) ≫ evaluation S 0`).

**Proof (via the chart projections, no unfolding of `twistMul`)** —
`twistMul_unit_right_of_app_one` (`TwistMulUnitRight`) for the abstract unit section
`u := twistUnitSection S`, whose only input is `twistUnitSection_app_one`: over every `π⁻¹U` (`U` affine),
`u(1) = evaluationLocal S 0 U (S.one.app U 1)`. The steps there:
1. Cancel `(ρ_ O(a)).inv` and check on sections `s ∈ Γ(O(a), V)`: `(ρ_).inv s = s ⊗ 1`
   (`rightUnitor_inv_app_eq_tensorSections`), `(O(a) ◁ u)(s ⊗ 1) = s ⊗ u(1)` (`whiskerLeft_app_tensorSections`),
   `tensorIsoTensorObj.inv` turns `tensorSections` into `moduleTensorSection`; so the claim is
   `twistMul S a 0 (s ⊗ u(1)) = eqToHom s` in `Γ(O(a+0), V)`.
2. `O(a+0)` is a sheaf: it suffices to check on `V ⊓ π⁻¹U` for all affine `U` (`TopCat.Sheaf.eq_of_locally_eq'`),
   restriction commuting with `Hom.app`, `moduleTensorSection` and `1`.
3. Over `V ≤ π⁻¹U`, the chart projection `twistπ (a+0) U : O(a+0) ⟶ (c_U)_* O_U(a+0)` (Stacks 01LI) is injective on
   sections (`twistπ_app_injective`), commutes with `eqToHom` (`twistπ_app_eqToHom_app`, `eqToHom_pushforward_twist_app_val`)
   and turns `twistMul` into the pointwise product of homogeneous fractions (`twistπ_app_twistMul_app_val`); the chart
   value of `u(1)` is the constant `1` (`twistπ_app_unit_val`: `u(1)|_V` is the restriction of `evaluationLocal S 0 U (S.one 1)`,
   whose chart value is `(sectionsOf U 0 (S.one 1))/1 = 1/1 = 1` by `twistπ_app_evaluationLocal_val`,
   `sectionsOf_one_app_one`, `Localization.mk_one`). Pointwise the claim is `x · 1 = x`.

**Edge cases**: `a` may be negative or `0`; `X = ∅` trivial. No hypothesis on `S` beyond being a graded
quasi-coherent algebra. -/
theorem twistMul_unit_right (a : ℤ) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S a ◁ twistUnitSection S) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.relativeProj.twist S a)
          (AlgebraicGeometry.Scheme.relativeProj.twist S 0)).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S a 0 =
      (ρ_ (AlgebraicGeometry.Scheme.relativeProj.twist S a)).hom ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_zero a).symm) :=
  twistMul_unit_right_of_app_one S a (twistUnitSection S) (twistUnitSection_app_one S)

/-- The block multiplication `μ_{e,e'} : L_e ⊗ L_{e'} ⟶ L_{e+e'}` with `L_e := O(qe) ⊗ π^*Q^{⊗e}`:
`twistPullbackMul` followed by the index transport `qe + qe' = q(e+e')` and `π^*(tensorPowAddIso Q e e')⁻¹`. -/
noncomputable def twistPullbackPowMul (q : ℕ) (Q : X.Modules) (e e' : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)))
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e' : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e'))) ⟶
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * (e + e') : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q (e + e'))) :=
  twistPullbackMul S ((q * e : ℕ) : ℤ) ((q * e' : ℕ) : ℤ)
      (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) (AlgebraicGeometry.Scheme.Modules.tensorPow Q e') ≫
    AlgebraicGeometry.Scheme.Modules.tensorMapHom
      (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S)
        (show ((q * e : ℕ) : ℤ) + ((q * e' : ℕ) : ℤ) = ((q * (e + e') : ℕ) : ℤ) by push_cast; ring)))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
          (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso Q e e').inv))

theorem twistPullbackPowMul_isIso (q : ℕ) (Q : X.Modules) (e e' : ℕ)
    [IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMul S ((q * e : ℕ) : ℤ) ((q * e' : ℕ) : ℤ))] :
    IsIso (twistPullbackPowMul S q Q e e') := by
  unfold twistPullbackPowMul; infer_instance

attribute [local instance] twistPullbackPowMul_isIso  -- file-local

end AlgebraicGeometry.Scheme.relativeProj

end
