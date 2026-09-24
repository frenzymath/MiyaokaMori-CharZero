import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorSheafificationComparison

/-! # The evaluation map `𝓗om(L, O_X) ⊗ L ⟶ O_X` of a line bundle is an isomorphism

Stacks 01CT / 0B8K (`lemma-invertible`: the dual of an invertible sheaf and the evaluation map). The
main statements are in `Stacks01ct` (`SheafOfModules.IsLineBundle.isIso_tensorDualEval`,
`tensor_dual_iso`); this module only proves `isIso_internalHomEval_unit`: for a line bundle `L`,
`internalHomEval L O_X : 𝓗om(L,O_X) ⊗ L ⟶ O_X` is an isomorphism. It is a separate module for
compile-time reasons.

Route (local check, not through stalks):
* `sheafifyTensorTo ≫ ev = L(p) ≫ ε` (`sheafifyTensorTo_comp_internalHomEval_eq`), where
  `p = internalHomEvalPre L : G 𝓗om ⊗ G L ⟶ G O_X` is the presheaf transpose of `ev` under the
  sheafification adjunction, `ε` is the sheafification counit (an isomorphism), and `sheafifyTensorTo`
  is the `hom` of `tensorIsoTensorObj` (an isomorphism).
* The value of `p` on pure tensors (`internalHomEvalPre_tmul_unit`): `p(η χ ⊗ a) = χ(a)`, from the
  definition of `tensorSections` and `internalHomEval_tensorSections_unit`; the inverse of the
  sheafification unit `η : 𝓗om presheaf → G 𝓗om` is `c₀ = internalHomEvalCurry` (`internalHomPresheaf`
  is already a sheaf).
* Local bijectivity: on a frame open `W` of `L` (frame `e`, `exists_frame_le`), the dual frame
  `e^∨ := (x ↦ coord_e(x) • 1)` (`IsFrame.dualFrameLocal`, written directly as a section of the
  internal Hom presheaf, not through `dualSheaf` — that definitional equality check is too expensive)
  satisfies `e^∨(r • e) = r`, and every section `χ` of the `𝓗om` presheaf on `W` is `χ(e) • e^∨`
  (`IsFrame.eq_smul_dualFrameLocal`); hence every `z ∈ 𝓗om(W) ⊗ L(W)` equals `e^∨ ⊗ (p(z) • e)`
  (`internalHomEvalLin_eq_tmul`; the tensor computation is done in the ordinary tensor product
  `Γ(𝓗om,W) ⊗[Γ(X,W)] Γ(L,W)`, definitionally `(G 𝓗om ⊗ G L)(W)`), so `p` is locally surjective
  (`r ↦ e^∨ ⊗ (r • e)`) and locally injective (`p z₁ = p z₂ ⇒ z₁|_W = z₂|_W`).
* A locally bijective map becomes an isomorphism after sheafification of modules:
  `moduleSheafification_map_isIso_of_locallyBijective`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

set_option backward.isDefEq.respectTransparency false

/-- The presheaf transpose `G 𝓗om ⊗ G L ⟶ G O` of the evaluation morphism `𝓗om(L,O) ⊗ L ⟶ O` under
the sheafification adjunction (the domain is that of `sheafifyTensorTo`, not `Modules.tensor`). -/
def internalHomEvalPre (L : X.Modules) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
        ((forgetZ X).obj L) ⟶
      (forgetZ X).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (adjZ X).homEquiv _ _
    (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
        (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)) L ≫
      AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf))

/-- `sheafifyTensorTo ≫ ev = L(p) ≫ ε` (sheafification adjunction). -/
theorem sheafifyTensorTo_comp_internalHomEval_eq (L : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
        (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)) L ≫
      AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf) =
    (sheafifyZ X).map (internalHomEvalPre L) ≫
      (adjZ X).counit.app (SheafOfModules.unit X.ringCatSheaf) :=
  (((adjZ X).homEquiv _ _).symm_apply_apply _).symm.trans ((adjZ X).homEquiv_counit _ _ _)

/-- The value of `p` on a section equals the value of `ev` on `sheafifyTensorTo (η z)`. -/
theorem internalHomEvalPre_app (L : X.Modules) (U : X.Opens)
    (z : (CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
      ((forgetZ X).obj L)).obj (Opposite.op U)) :
    (internalHomEvalPre L).app (Opposite.op U) z =
      (AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf)).val.app
        (Opposite.op U)
        ((AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
          (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)) L).val.app
          (Opposite.op U)
          (((adjZ X).unit.app (CategoryTheory.MonoidalCategoryStruct.tensorObj
            ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
            ((forgetZ X).obj L))).app (Opposite.op U) z)) := by
  have h := congrArg (fun k => _root_.PresheafOfModules.Hom.app k (Opposite.op U) z)
    ((adjZ X).homEquiv_unit _ _ (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
        (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)) L ≫
      AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf)))
  simp only at h
  exact h

/-- `p(η χ ⊗ a) = χ(𝟙 U)(a)`. -/
theorem internalHomEvalPre_tmul_unit (L : X.Modules) (U : X.Opens)
    (χ : (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf L
      (SheafOfModules.unit X.ringCatSheaf)).obj (Opposite.op U)) (a : Γ(L, U)) :
    (internalHomEvalPre L).app (Opposite.op U)
      (TensorProduct.tmul _ (((adjZ X).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf L
        (SheafOfModules.unit X.ringCatSheaf))).app (Opposite.op U) χ) a) =
      (χ.1 (CategoryTheory.Over.mk (𝟙 U))) a := by
  rw [internalHomEvalPre_app]
  exact AlgebraicGeometry.Scheme.Modules.internalHomEval_tensorSections_unit L
    (SheafOfModules.unit X.ringCatSheaf) U χ a

/-- `c₀ (η χ) = χ` (sectionwise). -/
theorem internalHomEvalCurry_unit_app (G H : X.Modules) (U : X.Opens)
    (χ : (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H).obj (Opposite.op U)) :
    (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H).app (Opposite.op U)
      (((adjZ X).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)).app
        (Opposite.op U) χ) = χ := by
  have h := congrArg (fun k => _root_.PresheafOfModules.Hom.app k (Opposite.op U) χ)
    (AlgebraicGeometry.Scheme.Modules.unit_comp_internalHomEvalCurry G H)
  simp only at h
  exact h

/-- `η (c₀ φ) = φ` (sectionwise). -/
theorem unit_internalHomEvalCurry_app (G H : X.Modules) (U : X.Opens)
    (φ : Γ(AlgebraicGeometry.Scheme.Modules.internalHom G H, U)) :
    ((adjZ X).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)).app (Opposite.op U)
      ((AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H).app (Opposite.op U) φ) = φ := by
  have h := congrArg (fun k => _root_.PresheafOfModules.Hom.app k (Opposite.op U) φ)
    (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry_comp_unit G H)
  simp only at h
  exact h

/-- `r • 1 = r` on sections of the structure sheaf (the `Γ(X, U)`-module structure of `Γ(O_X, U)` is
multiplication). -/
theorem unit_toSpanSingleton_one_apply (U : X.Opens) (r : Γ(X, U)) :
    (LinearMap.toSpanSingleton Γ(X, U) Γ(SheafOfModules.unit X.ringCatSheaf, U) (1 : Γ(X, U))) r = r :=
  mul_one r

/-- The dual frame `e^∨` of a frame `e`, as a section over `W` of the internal Hom presheaf
`𝓗om(L, O_X)`: `x ↦ coord_e(x) • 1`. -/
def IsFrame.dualFrameLocal {L : X.Modules} {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e) :
    AlgebraicGeometry.Scheme.Modules.localHomSubmodule L (SheafOfModules.unit X.ringCatSheaf) W :=
  ⟨fun V => (LinearMap.toSpanSingleton Γ(X, V.left) Γ(SheafOfModules.unit X.ringCatSheaf, V.left)
      (1 : Γ(X, V.left))).comp (hf.coordEquiv (leOfHom V.hom)).toLinearMap, by
    intro V V' i x
    show (LinearMap.toSpanSingleton Γ(X, V.left) Γ(SheafOfModules.unit X.ringCatSheaf, V.left) (1 : Γ(X, V.left)))
        (hf.coordEquiv (leOfHom V.hom) (L.presheaf.map i.left.op x)) =
      (AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).map i.left.op
        ((LinearMap.toSpanSingleton Γ(X, V'.left) Γ(SheafOfModules.unit X.ringCatSheaf, V'.left) (1 : Γ(X, V'.left)))
          (hf.coordEquiv (leOfHom V'.hom) x))
    rw [unit_toSpanSingleton_one_apply, unit_toSpanSingleton_one_apply]
    exact hf.coord_map (leOfHom i.left) (leOfHom V'.hom) x⟩

/-- The value on `a` over `U` of a section `χ` of the internal Hom presheaf, as an element of `Γ(X, U)`. -/
def localHomEval {L : X.Modules} {U : X.Opens}
    (χ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule L (SheafOfModules.unit X.ringCatSheaf) U)
    (a : Γ(L, U)) : Γ(X, U) :=
  χ.1 (CategoryTheory.Over.mk (𝟙 U)) a

theorem localHomEval_smul {L : X.Modules} {U : X.Opens}
    (χ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule L (SheafOfModules.unit X.ringCatSheaf) U)
    (r : Γ(X, U)) (a : Γ(L, U)) : localHomEval χ (r • a) = r * localHomEval χ a := by
  unfold localHomEval
  rw [LinearMap.map_smul]
  rfl

/-- `e^∨(r • e) = r`. -/
theorem IsFrame.localHomEval_dualFrameLocal {L : X.Modules} {W : X.Opens} {e : Γ(L, W)}
    (hf : IsFrame L W e) (r : Γ(X, W)) : localHomEval hf.dualFrameLocal (r • e) = r := by
  show (LinearMap.toSpanSingleton Γ(X, W) Γ(SheafOfModules.unit X.ringCatSheaf, W) (1 : Γ(X, W)))
    (hf.coordEquiv (leOfHom (CategoryTheory.Over.mk (𝟙 W)).hom) (r • e)) = r
  rw [unit_toSpanSingleton_one_apply]
  have he : L.res (leOfHom (CategoryTheory.Over.mk (𝟙 W)).hom) e = e := res_self L e
  exact hf.coord_unique _ _ r (congrArg (fun y => r • y) he)

/-- Every section of the internal Hom presheaf over a frame open `W` is a multiple of `e^∨`:
`χ = χ(e) • e^∨`. -/
theorem IsFrame.eq_smul_dualFrameLocal {L : X.Modules} {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e)
    (χ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule L (SheafOfModules.unit X.ringCatSheaf) W) :
    localHomEval χ e • hf.dualFrameLocal = χ := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  have hx : hf.coord (leOfHom V.hom) x • L.res (leOfHom V.hom) e = x := hf.coord_smul_frame _ x
  have hχ : χ.1 V (L.res (leOfHom V.hom) e) =
      (AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).map V.hom.op
        (χ.1 (CategoryTheory.Over.mk (𝟙 W)) e) :=
    χ.2 V (CategoryTheory.Over.mk (𝟙 W)) (CategoryTheory.Over.homMk V.hom (CategoryTheory.Category.comp_id _)) e
  show X.presheaf.map V.hom.op (localHomEval χ e) •
      (LinearMap.toSpanSingleton Γ(X, V.left) Γ(SheafOfModules.unit X.ringCatSheaf, V.left) (1 : Γ(X, V.left)))
        (hf.coordEquiv (leOfHom V.hom) x) = χ.1 V x
  rw [unit_toSpanSingleton_one_apply]
  conv_rhs => rw [← hx, LinearMap.map_smul, hχ]
  change (X.presheaf.map V.hom.op (localHomEval χ e) : Γ(X, V.left)) * hf.coord (leOfHom V.hom) x =
    hf.coord (leOfHom V.hom) x * X.presheaf.map V.hom.op (localHomEval χ e)
  exact mul_comm _ _

/-- `e^∨` as a section of the sheaf `𝓗om(L, O_X)` (the image under the sheafification unit). -/
def IsFrame.dualFrameSheaf {L : X.Modules} {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e) :
    Γ(AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf), W) :=
  ((adjZ X).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf L
    (SheafOfModules.unit X.ringCatSheaf))).app (Opposite.op W) hf.dualFrameLocal

/-- A section `φ` of the sheaf `𝓗om(L, O_X)` viewed as a presheaf section: `c₀ φ`. -/
def toLocalHom {L : X.Modules} {U : X.Opens}
    (φ : Γ(AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf), U)) :
    AlgebraicGeometry.Scheme.Modules.localHomSubmodule L (SheafOfModules.unit X.ringCatSheaf) U :=
  (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry L (SheafOfModules.unit X.ringCatSheaf)).app
    (Opposite.op U) φ

/-- Every section of the sheaf `𝓗om(L, O_X)` over a frame open `W` is a multiple of `e^∨`:
`φ = (c₀ φ)(e) • e^∨`. -/
theorem IsFrame.eq_smul_dualFrameSheaf {L : X.Modules} {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e)
    (φ : Γ(AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf), W)) :
    localHomEval (toLocalHom φ) e • hf.dualFrameSheaf = φ := by
  have h1 := hf.eq_smul_dualFrameLocal (toLocalHom φ)
  have h2 := unit_internalHomEvalCurry_app L (SheafOfModules.unit X.ringCatSheaf) W φ
  unfold IsFrame.dualFrameSheaf
  conv_rhs => rw [← h2]
  change _ = ((adjZ X).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf L
    (SheafOfModules.unit X.ringCatSheaf))).app (Opposite.op W) (toLocalHom φ)
  conv_rhs => rw [← h1]
  exact ((((adjZ X).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf L
    (SheafOfModules.unit X.ringCatSheaf))).app (Opposite.op W)).hom.map_smul _ _).symm

/-- `p` on sections over `U`, written as a `Γ(X, U)`-linear map on the ordinary tensor product
`Γ(𝓗om, U) ⊗[Γ(X, U)] Γ(L, U)` (definitionally `(G 𝓗om ⊗ G L)(U)`; this makes the standard tensor
product lemmas directly applicable). -/
def internalHomEvalLin (L : X.Modules) (U : X.Opens) :
    Γ(AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf), U) ⊗[Γ(X, U)]
      Γ(L, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun z := (internalHomEvalPre L).app (Opposite.op U) z
  map_add' z₁ z₂ := map_add ((internalHomEvalPre L).app (Opposite.op U)).hom z₁ z₂
  map_smul' r z := ((internalHomEvalPre L).app (Opposite.op U)).hom.map_smul r z

/-- `p(φ ⊗ a) = (c₀ φ)(a)`. -/
theorem internalHomEvalLin_tmul (L : X.Modules) (U : X.Opens)
    (φ : Γ(AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf), U))
    (a : Γ(L, U)) :
    internalHomEvalLin L U (φ ⊗ₜ[Γ(X, U)] a) = localHomEval (toLocalHom φ) a := by
  have h2 := unit_internalHomEvalCurry_app L (SheafOfModules.unit X.ringCatSheaf) U φ
  conv_lhs => rw [← h2]
  exact internalHomEvalPre_tmul_unit L U (toLocalHom φ) a

/-- On a frame open, every `z ∈ 𝓗om(W) ⊗ L(W)` is `e^∨ ⊗ (p(z) • e)`. -/
theorem internalHomEvalLin_eq_tmul {L : X.Modules} {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e)
    (z : Γ(AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf), W) ⊗[Γ(X, W)]
      Γ(L, W)) :
    z = hf.dualFrameSheaf ⊗ₜ[Γ(X, W)] (internalHomEvalLin L W z • e) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_smul, TensorProduct.tmul_zero]
  | tmul φ a =>
    rw [internalHomEvalLin_tmul]
    have ha : hf.coord le_rfl a • e = a := by
      have h := hf.coord_smul_frame le_rfl a
      rwa [res_self] at h
    have hφ := hf.eq_smul_dualFrameSheaf φ
    have hval : localHomEval (toLocalHom φ) a =
        hf.coord le_rfl a * localHomEval (toLocalHom φ) e := by
      conv_lhs => rw [← ha]
      exact localHomEval_smul _ _ _
    rw [hval]
    conv_lhs => rw [← ha, ← hφ]
    rw [TensorProduct.smul_tmul, smul_smul, mul_comm]
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, add_smul, TensorProduct.tmul_add]
    exact congrArg₂ (· + ·) h₁ h₂

/-- `p` is locally surjective: `r|_W = p(e^∨ ⊗ (r|_W • e))`. -/
theorem internalHomEvalPre_isLocallySurjective (L : X.Modules) [L.IsLineBundle] :
    _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (internalHomEvalPre L) := by
  refine ⟨fun {U} r ↦ ?_⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨W, hWU, hxW, e, hf⟩ := exists_frame_le L hx
  let r' : Γ(X, W) := X.presheaf.map (homOfLE hWU).op r
  refine ⟨W, homOfLE hWU, ⟨(hf.dualFrameSheaf ⊗ₜ[Γ(X, W)] (r' • e) :
    Γ(AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf), W) ⊗[Γ(X, W)]
      Γ(L, W)), ?_⟩, hxW⟩
  change internalHomEvalLin L W (hf.dualFrameSheaf ⊗ₜ[Γ(X, W)] (r' • e)) = r'
  rw [internalHomEvalLin_tmul]
  unfold toLocalHom IsFrame.dualFrameSheaf
  rw [internalHomEvalCurry_unit_app]
  exact hf.localHomEval_dualFrameLocal r'

/-- `p` is locally injective: `p z₁ = p z₂ ⇒ z₁|_W = z₂|_W`. -/
theorem internalHomEvalPre_isLocallyInjective (L : X.Modules) [L.IsLineBundle] :
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (internalHomEvalPre L) := by
  refine ⟨fun {U} z₁ z₂ heq ↦ ?_⟩
  change (internalHomEvalPre L).app U z₁ = (internalHomEvalPre L).app U z₂ at heq
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨W, hWU, hxW, e, hf⟩ := exists_frame_le L hx
  refine ⟨W, homOfLE hWU, ?_, hxW⟩
  change (CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
      ((forgetZ X).obj L)).map (homOfLE hWU).op z₁ =
    (CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
      ((forgetZ X).obj L)).map (homOfLE hWU).op z₂
  have h1 := internalHomEvalLin_eq_tmul hf
    ((CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
      ((forgetZ X).obj L)).map (homOfLE hWU).op z₁)
  have h2 := internalHomEvalLin_eq_tmul hf
    ((CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
      ((forgetZ X).obj L)).map (homOfLE hWU).op z₂)
  have hnat : internalHomEvalLin L W ((CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
      ((forgetZ X).obj L)).map (homOfLE hWU).op z₁) =
    internalHomEvalLin L W ((CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((forgetZ X).obj (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)))
      ((forgetZ X).obj L)).map (homOfLE hWU).op z₂) := by
    change (internalHomEvalPre L).app (Opposite.op W) _ = (internalHomEvalPre L).app (Opposite.op W) _
    rw [_root_.PresheafOfModules.naturality_apply, _root_.PresheafOfModules.naturality_apply, heq]
  exact h1.trans ((congrArg (fun c => hf.dualFrameSheaf ⊗ₜ[Γ(X, W)] (c • e)) hnat).trans h2.symm)

/-- The evaluation `ev : 𝓗om(L, O_X) ⊗ L ⟶ O_X` is an isomorphism (`L` a line bundle). -/
theorem isIso_internalHomEval_unit (L : X.Modules) [L.IsLineBundle] :
    CategoryTheory.IsIso
      (AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf)) := by
  have := internalHomEvalPre_isLocallyInjective L
  have := internalHomEvalPre_isLocallySurjective L
  have : CategoryTheory.IsIso ((sheafifyZ X).map (internalHomEvalPre L)) :=
    AlgebraicGeometry.Scheme.Modules.moduleSheafification_map_isIso_of_locallyBijective _
  have hciso : CategoryTheory.IsIso
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit := inferInstance
  have : CategoryTheory.IsIso ((adjZ X).counit.app (SheafOfModules.unit X.ringCatSheaf)) :=
    @CategoryTheory.NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hciso _
  have hcomp : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
        (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)) L ≫
      AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf)) := by
    rw [sheafifyTensorTo_comp_internalHomEval_eq]
    exact CategoryTheory.IsIso.comp_isIso
  have : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
      (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)) L) :=
    ⟨⟨AlgebraicGeometry.Scheme.Modules.tensorToSheafify _ L,
      AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo_comp_tensorToSheafify _ L,
      AlgebraicGeometry.Scheme.Modules.tensorToSheafify_comp_sheafifyTensorTo _ L⟩⟩
  exact CategoryTheory.IsIso.of_isIso_comp_left (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
    (AlgebraicGeometry.Scheme.Modules.internalHom L (SheafOfModules.unit X.ringCatSheaf)) L) _

set_option maxHeartbeats 1000000 in
/-- The same conclusion with the domain of `ev` written as `dual L ⊗ L` (`dual L = internalHom L O_X`
is a definitional equality, but its check is expensive and is done only once, here). -/
theorem isIso_internalHomEval_dual {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    CategoryTheory.IsIso
      (AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf) :
        CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
          (AlgebraicGeometry.Scheme.Modules.dual L) L ⟶ SheafOfModules.unit X.ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.isIso_internalHomEval_unit L

end AlgebraicGeometry.Scheme.Modules

end
