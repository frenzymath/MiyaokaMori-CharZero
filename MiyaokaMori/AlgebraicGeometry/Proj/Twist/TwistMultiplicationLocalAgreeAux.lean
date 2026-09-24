import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.TwistMultiplicationRestrictTensorSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplicationChartSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf

/-! # Generic auxiliaries for the local agreement of the twist multiplication

Generic (variable-only) lemmas for `relativeProj.twistMulLocal_agree_of_le` (module
`TwistMultiplication`), so that all concrete instantiations are first-order and kernel-cheap.

1. `twistMulLocalShape` — the exact eight-factor body of `relativeProj.twistMulLocal` with atomic parameters
   (a `@[reducible] def`: instance search still sees the composite, but the kernel treats it as a regular
   definition, so `twistMulLocal S a b U = twistMulLocalShape …` is a one-step delta; see the docstring).
2. `twistMulNormalForm` and `twistMulLocalShape_comp_eq`: postcomposing the shape with the third chart comparison
   isomorphism cancels all the auxiliary isomorphisms (naturality of `restrictFunctorIsoPullback`,
   `tensorHom_comp_tensorHom`), leaving `R_ι(tITO) ≫ (rTOI ι) ≫ (t₁ ⊗ t₂) ≫ (rTOI e)⁻¹ ≫ R_e(tITO⁻¹ ≫ μ) ≫ rFIP`.
3. `twistMulNormalForm_app`: the normal form on a pure tensor section `η(x ⊗ y)` (via the section formulas of
   `TwistMultiplicationRestrictTensorSections`).
4. `twistMulLocalShape_app_unit_tmul`: the **pointwise engine** — given section formulas for the chart comparison
   maps (`twistAffineHom_app`-shaped), for `μ` on pure tensors, and compatibility of the product with transport,
   `π₃ (shape.app A (η(x ⊗ y))) = m' (π₁ x) (π₂ y)`.
5. `Proj`-level facts: restriction commutes with `twistSectionMul` (`rfl`), `Proj.twistMul` on `η(s ⊗ t)` is
   `twistSectionMul` (Mathlib `Adjunction.homEquiv_counit` + sheafification triangle identity), and the transition
   map θ of `ProjTwistPushTransition` is multiplicative (pointwise `Localization.localRingHom`).

**Kernel performance rules used throughout**: the kernel's
"compare arguments first" optimisation applies only to *regular* definitions; `abbrev`s and projection functions
(`≫`, `NatTrans.app`, `Functor.obj`, `Functor.map`) are unfolded wholesale. Hence a defeq check between two
`≫`-composites that differ anywhere inside costs minutes, while `congrArg`/`Eq.trans` between syntactically identical
terms and first-order instantiation of generic lemmas cost nothing. Do not restate these lemmas with different
spellings; instantiate them.

Sources: Stacks 01NR (multiplication corresponds chart by chart), 01MX (pointwise description of θ);
Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

theorem presheafMapW_eqToHom_injective {Z : AlgebraicGeometry.Scheme.{u}} (N : Z.Modules) {V W : Z.Opens}
    (h : V = W) : Function.Injective (presheafMapW N (CategoryTheory.eqToHom h)) := by
  subst h
  intro p q hpq
  have e : presheafMapW N (CategoryTheory.eqToHom (rfl : V = V)) = 𝟙 _ := by
    unfold presheafMapW
    rw [CategoryTheory.eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rw [e, ConcreteCategory.id_apply, ConcreteCategory.id_apply] at hpq
  exact hpq

theorem rFIPhomApp_injective {Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ Z)
    (hf : AlgebraicGeometry.IsOpenImmersion f) (N : Z.Modules) (A : Y.Opens) :
    Function.Injective (rFIPhomApp f hf N A) := by
  intro p q hpq
  have k := fun v => ConcreteCategory.congr_hom (rFIPhomApp_comp_inv_app f hf N A) v
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at k
  exact (k p).symm.trans ((congrArg (fun w => (((@restrictFunctorIsoPullback Y Z f hf).inv.app N).app A) w) hpq).trans
    (k q))

variable {Y P Z : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι]
  (e : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion e]

def twistMulNormalForm (M₁ M₂ : P.Modules) (N₁ N₂ N₃ : Z.Modules)
    (t₁ : M₁.restrict ι ⟶ (pullback e).obj N₁) (t₂ : M₂.restrict ι ⟶ (pullback e).obj N₂)
    (μ : tensor N₁ N₂ ⟶ N₃) :
    (tensor M₁ M₂).restrict ι ⟶ (pullback e).obj N₃ :=
  (restrictFunctor ι).map (tensorIsoTensorObj M₁ M₂).hom ≫ (restrictTensorObjIso ι M₁ M₂).hom ≫
    ((t₁ ≫ (restrictFunctorIsoPullback e).inv.app N₁) ⊗ₘ (t₂ ≫ (restrictFunctorIsoPullback e).inv.app N₂)) ≫
    (restrictTensorObjIso e N₁ N₂).inv ≫ (restrictFunctor e).map ((tensorIsoTensorObj N₁ N₂).inv ≫ μ) ≫
    (restrictFunctorIsoPullback e).hom.app N₃

theorem twistMulShape_comp_eq (M₁ M₂ M₃ : P.Modules) (N₁ N₂ N₃ : Z.Modules)
    (i₁ : M₁.restrict ι ≅ (pullback e).obj N₁) (i₂ : M₂.restrict ι ≅ (pullback e).obj N₂)
    (i₃ : M₃.restrict ι ≅ (pullback e).obj N₃)
    (t₁ : M₁.restrict ι ⟶ (pullback e).obj N₁) (t₂ : M₂.restrict ι ⟶ (pullback e).obj N₂)
    (t₃ : M₃.restrict ι ⟶ (pullback e).obj N₃)
    (h₁ : i₁.hom = t₁) (h₂ : i₂.hom = t₂) (h₃ : i₃.hom = t₃) (μ : tensor N₁ N₂ ⟶ N₃) :
    ((restrictFunctorIsoPullback ι).hom.app (tensor M₁ M₂) ≫
      (pullbackTensorIsoOpen ι M₁ M₂).hom ≫
      (tensorIsoTensorObj _ _).hom ≫
      ((((restrictFunctorIsoPullback ι).app M₁).symm ≪≫ i₁).hom ⊗ₘ
        (((restrictFunctorIsoPullback ι).app M₂).symm ≪≫ i₂).hom) ≫
      (tensorIsoTensorObj _ _).inv ≫
      (pullbackTensorIsoOpen e N₁ N₂).inv ≫
      (pullback e).map μ ≫ i₃.inv) ≫ t₃ = twistMulNormalForm ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ := by
  subst h₁ h₂ h₃
  unfold twistMulNormalForm pullbackTensorIsoOpen pullbackTensorObjIsoOpen
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    tensorIso_hom, tensorIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← NatTrans.naturality_assoc (restrictFunctorIsoPullback ι).hom (tensorIsoTensorObj M₁ M₂).hom]
  rw [Iso.hom_inv_id_app_assoc]
  rw [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc,
    tensorHom_comp_tensorHom_assoc]
  rw [← Functor.map_comp, ← NatTrans.naturality]

theorem twistMulNormalForm_val_app (M₁ M₂ : P.Modules) (N₁ N₂ N₃ : Z.Modules)
    (t₁ : M₁.restrict ι ⟶ (pullback e).obj N₁) (t₂ : M₂.restrict ι ⟶ (pullback e).obj N₂)
    (μ : tensor N₁ N₂ ⟶ N₃) (A : Y.Opens)
    (x : M₁.val.obj (op (ι ''ᵁ A))) (y : M₂.val.obj (op (ι ''ᵁ A))) :
    (twistMulNormalForm ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ).val.app (op A)
        (((shAdj P).unit.app ((shG P).obj M₁ ⊗ (shG P).obj M₂)).app (op (ι ''ᵁ A)) (TensorProduct.tmul _ x y)) =
      ((restrictFunctorIsoPullback e).hom.app N₃).val.app (op A)
        (μ.val.app (op (e ''ᵁ A))
          (((shAdj Z).unit.app ((shG Z).obj N₁ ⊗ (shG Z).obj N₂)).app (op (e ''ᵁ A))
            (TensorProduct.tmul _
              (((restrictFunctorIsoPullback e).inv.app N₁).val.app (op A) (t₁.val.app (op A) x))
              (((restrictFunctorIsoPullback e).inv.app N₂).val.app (op A) (t₂.val.app (op A) y))))) := by
  set a₁ := (restrictFunctor ι).map (tensorIsoTensorObj M₁ M₂).hom with ha₁
  set a₂ := (restrictTensorObjIso ι M₁ M₂).hom with ha₂
  set a₃ := ((t₁ ≫ (restrictFunctorIsoPullback e).inv.app N₁) ⊗ₘ (t₂ ≫ (restrictFunctorIsoPullback e).inv.app N₂))
    with ha₃
  set a₄ := (restrictTensorObjIso e N₁ N₂).inv with ha₄
  set a₅ := (restrictFunctor e).map ((tensorIsoTensorObj N₁ N₂).inv ≫ μ) with ha₅
  set a₆ := (restrictFunctorIsoPullback e).hom.app N₃ with ha₆
  set z := ((shAdj P).unit.app ((shG P).obj M₁ ⊗ (shG P).obj M₂)).app (op (ι ''ᵁ A)) (TensorProduct.tmul _ x y)
    with hz
  set u := ((restrictFunctorIsoPullback e).inv.app N₁).val.app (op A) (t₁.val.app (op A) x) with hu
  set v := ((restrictFunctorIsoPullback e).inv.app N₂).val.app (op A) (t₂.val.app (op A) y) with hv
  have h0 : (twistMulNormalForm ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ).val.app (op A) z =
      a₆.val.app (op A) (a₅.val.app (op A) (a₄.val.app (op A) (a₃.val.app (op A)
        (a₂.val.app (op A) (a₁.val.app (op A) z))))) := rfl
  refine h0.trans ?_
  have h1 : a₁.val.app (op A) z = tensorSections M₁ M₂ (ι ''ᵁ A) x y := rfl
  have h2 : a₂.val.app (op A) (tensorSections M₁ M₂ (ι ''ᵁ A) x y) =
      tensorSections (M₁.restrict ι) (M₂.restrict ι) A x y :=
    restrictTensorObjIso_hom_app_tensorSections ι M₁ M₂ A x y
  have h3 : a₃.val.app (op A) (tensorSections (M₁.restrict ι) (M₂.restrict ι) A x y) =
      tensorSections (N₁.restrict e) (N₂.restrict e) A u v :=
    tensorHom_tensorSections_restrict ι (t₁ ≫ (restrictFunctorIsoPullback e).inv.app N₁)
      (t₂ ≫ (restrictFunctorIsoPullback e).inv.app N₂) A x y
  have h4 : a₄.val.app (op A) (tensorSections (N₁.restrict e) (N₂.restrict e) A u v) =
      tensorSections N₁ N₂ (e ''ᵁ A) u v :=
    restrictTensorObjIso_inv_app_tensorSections e N₁ N₂ A u v
  have h5 : a₅.val.app (op A) (tensorSections N₁ N₂ (e ''ᵁ A) u v) =
      μ.val.app (op (e ''ᵁ A)) ((tensorIsoTensorObj N₁ N₂).inv.val.app (op (e ''ᵁ A))
        (tensorSections N₁ N₂ (e ''ᵁ A) u v)) := rfl
  have h6 : (tensorIsoTensorObj N₁ N₂).inv.val.app (op (e ''ᵁ A)) (tensorSections N₁ N₂ (e ''ᵁ A) u v) =
      ((shAdj Z).unit.app ((shG Z).obj N₁ ⊗ (shG Z).obj N₂)).app (op (e ''ᵁ A)) (TensorProduct.tmul _ u v) :=
    tensorToSheafify_tensorSections N₁ N₂ (e ''ᵁ A) u v
  rw [h1, h2, h3, h4, h5, h6]

/-- The unit of sheafification on `G N₁ ⊗ G N₂` and on `moduleTensorPresheaf N₁ N₂` agree
(definitionally, for generic `N₁ N₂`). -/
theorem unit_app_tensorObj_eq_unit_app_moduleTensorPresheaf (N₁ N₂ : Z.Modules) (U : Z.Opens)
    (u : N₁.val.obj (op U)) (v : N₂.val.obj (op U)) :
    ((shAdj Z).unit.app ((shG Z).obj N₁ ⊗ (shG Z).obj N₂)).app (op U) (TensorProduct.tmul _ u v) =
      ((shAdj Z).unit.app (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf N₁ N₂)).app (op U) (TensorProduct.tmul _ u v) := rfl


theorem twistMulNormalForm_app (M₁ M₂ : P.Modules) (N₁ N₂ N₃ : Z.Modules)
    (t₁ : M₁.restrict ι ⟶ (pullback e).obj N₁) (t₂ : M₂.restrict ι ⟶ (pullback e).obj N₂)
    (μ : tensor N₁ N₂ ⟶ N₃) (A : Y.Opens)
    (x : M₁.val.obj (op (ι ''ᵁ A))) (y : M₂.val.obj (op (ι ''ᵁ A))) :
    (twistMulNormalForm ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ).app A
        (((shAdj P).unit.app ((shG P).obj M₁ ⊗ (shG P).obj M₂)).app (op (ι ''ᵁ A)) (TensorProduct.tmul _ x y)) =
      ((restrictFunctorIsoPullback e).hom.app N₃).app A
        (μ.val.app (op (e ''ᵁ A))
          (((shAdj Z).unit.app (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf N₁ N₂)).app (op (e ''ᵁ A))
            (TensorProduct.tmul _
              (((restrictFunctorIsoPullback e).inv.app N₁).app A (t₁.app A x))
              (((restrictFunctorIsoPullback e).inv.app N₂).app A (t₂.app A y))))) :=
  twistMulNormalForm_val_app ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ A x y

/-- The exact shape of the body of `relativeProj.twistMulLocal`, with atomic parameters. It is an `abbrev` so that
instance search still sees the composite (`twistMulLocal_isIso` in `TwistPowerIso` does `unfold; infer_instance`),
while equations about `twistMulLocal` are proved by first-order instantiation of `twistMulLocalShape_comp_eq`
(unifying against the unfolded eight-factor composite takes more than 60 s). -/
@[reducible] def twistMulLocalShape (M₁ M₂ M₃ : P.Modules) (N₁ N₂ N₃ : Z.Modules)
    (i₁ : M₁.restrict ι ≅ (pullback e).obj N₁) (i₂ : M₂.restrict ι ≅ (pullback e).obj N₂)
    (i₃ : M₃.restrict ι ≅ (pullback e).obj N₃) (μ : tensor N₁ N₂ ⟶ N₃) :
    (tensor M₁ M₂).restrict ι ⟶ M₃.restrict ι :=
  (restrictFunctorIsoPullback ι).hom.app (tensor M₁ M₂) ≫
    (pullbackTensorIsoOpen ι M₁ M₂).hom ≫
    (tensorIsoTensorObj _ _).hom ≫
    ((((restrictFunctorIsoPullback ι).app M₁).symm ≪≫ i₁).hom ⊗ₘ
      (((restrictFunctorIsoPullback ι).app M₂).symm ≪≫ i₂).hom) ≫
    (tensorIsoTensorObj _ _).inv ≫
    (pullbackTensorIsoOpen e N₁ N₂).inv ≫
    (pullback e).map μ ≫ i₃.inv

theorem twistMulLocalShape_comp_eq (M₁ M₂ M₃ : P.Modules) (N₁ N₂ N₃ : Z.Modules)
    (i₁ : M₁.restrict ι ≅ (pullback e).obj N₁) (i₂ : M₂.restrict ι ≅ (pullback e).obj N₂)
    (i₃ : M₃.restrict ι ≅ (pullback e).obj N₃)
    (t₁ : M₁.restrict ι ⟶ (pullback e).obj N₁) (t₂ : M₂.restrict ι ⟶ (pullback e).obj N₂)
    (t₃ : M₃.restrict ι ⟶ (pullback e).obj N₃)
    (h₁ : i₁.hom = t₁) (h₂ : i₂.hom = t₂) (h₃ : i₃.hom = t₃) (μ : tensor N₁ N₂ ⟶ N₃) :
    twistMulLocalShape ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μ ≫ t₃ = twistMulNormalForm ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ :=
  twistMulShape_comp_eq ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ t₁ t₂ t₃ h₁ h₂ h₃ μ

/-- `g.app A (f.app A z) = h.app A z` when `f ≫ g = h` (equation form of `Hom.comp_app`). -/
theorem app_app_eq_of_comp_eq {M N K : Y.Modules} (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (hfg : f ≫ g = h)
    (A : Y.Opens) (z : Γ(M, A)) : g.app A (f.app A z) = h.app A z := by
  subst hfg
  rfl

/-- `((restrictFunctorIsoPullback f).inv.app N).app A` is a left inverse of `rFIPhomApp f hf N A`. -/
theorem rFIPhomApp_inv_app_apply {Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ Z)
    (hf : AlgebraicGeometry.IsOpenImmersion f) (N : Z.Modules) (A : Y.Opens)
    (p : Γ((@restrictFunctor Y Z f hf).obj N, A)) :
    ((@restrictFunctorIsoPullback Y Z f hf).inv.app N).app A (rFIPhomApp f hf N A p) = p := by
  have k := ConcreteCategory.congr_hom (rFIPhomApp_comp_inv_app f hf N A) p
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans (k.trans (ConcreteCategory.id_apply _))


/-- **Generic pointwise computation of a local multiplication.** Let `shape := twistMulLocalShape ι e … i₁ i₂ i₃ μ`
(the body of `relativeProj.twistMulLocal`). Suppose the chart comparison isomorphisms are given pointwise by
"chart sections" `πₙ` followed by transport along `j : e''A ⟶ W` (`h₁ h₂ h₃`, the form of `twistAffineHom_app`),
`μ` on pure tensor sections is a product `m` (`hμ`) compatible with transport along `j` (`hm`), and transport
along `j` is injective on `N₃` (`hj`). Then `π₃ (shape.app A (η(x ⊗ y))) = m' (π₁ x) (π₂ y)`.
All statements are generic, so the concrete instantiation is first-order (kernel-cheap). -/
theorem twistMulLocalShape_app_unit_tmul (M₁ M₂ M₃ : P.Modules) (N₁ N₂ N₃ : Z.Modules)
    (i₁ : M₁.restrict ι ≅ (pullback e).obj N₁) (i₂ : M₂.restrict ι ≅ (pullback e).obj N₂)
    (i₃ : M₃.restrict ι ≅ (pullback e).obj N₃)
    (t₁ : M₁.restrict ι ⟶ (pullback e).obj N₁) (t₂ : M₂.restrict ι ⟶ (pullback e).obj N₂)
    (t₃ : M₃.restrict ι ⟶ (pullback e).obj N₃)
    (hi₁ : i₁.hom = t₁) (hi₂ : i₂.hom = t₂) (hi₃ : i₃.hom = t₃) (μ : tensor N₁ N₂ ⟶ N₃)
    (A : Y.Opens) {W : Z.Opens} (j : e ''ᵁ A ⟶ W)
    (π₁ : Γ(M₁, ι ''ᵁ A) → Γ(N₁, W)) (π₂ : Γ(M₂, ι ''ᵁ A) → Γ(N₂, W)) (π₃ : Γ(M₃, ι ''ᵁ A) → Γ(N₃, W))
    (h₁ : ∀ v, t₁.app A v = rFIPhomApp e inferInstance N₁ A (presheafMapW N₁ j (π₁ v)))
    (h₂ : ∀ v, t₂.app A v = rFIPhomApp e inferInstance N₂ A (presheafMapW N₂ j (π₂ v)))
    (h₃ : ∀ v, t₃.app A v = rFIPhomApp e inferInstance N₃ A (presheafMapW N₃ j (π₃ v)))
    (m : Γ(N₁, e ''ᵁ A) → Γ(N₂, e ''ᵁ A) → Γ(N₃, e ''ᵁ A)) (m' : Γ(N₁, W) → Γ(N₂, W) → Γ(N₃, W))
    (hμ : ∀ (u : Γ(N₁, e ''ᵁ A)) (v : Γ(N₂, e ''ᵁ A)), μ.val.app (op (e ''ᵁ A))
      (((shAdj Z).unit.app (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf N₁ N₂)).app (op (e ''ᵁ A)) (TensorProduct.tmul _ u v)) = m u v)
    (hm : ∀ (s : Γ(N₁, W)) (t : Γ(N₂, W)),
      N₃.presheaf.map j.op (m' s t) = m (N₁.presheaf.map j.op s) (N₂.presheaf.map j.op t))
    (hj : Function.Injective (presheafMapW N₃ j))
    (x : Γ(M₁, ι ''ᵁ A)) (y : Γ(M₂, ι ''ᵁ A)) :
    π₃ ((twistMulLocalShape ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μ).app A
        (((shAdj P).unit.app ((shG P).obj M₁ ⊗ (shG P).obj M₂)).app (op (ι ''ᵁ A)) (TensorProduct.tmul _ x y))) =
      m' (π₁ x) (π₂ y) := by
  set z := ((shAdj P).unit.app ((shG P).obj M₁ ⊗ (shG P).obj M₂)).app (op (ι ''ᵁ A)) (TensorProduct.tmul _ x y)
    with hz
  set w := (twistMulLocalShape ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μ).app A z with hw
  have s1 : t₃.app A w = (twistMulNormalForm ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ).app A z :=
    app_app_eq_of_comp_eq _ _ _ (twistMulLocalShape_comp_eq ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ t₁ t₂ t₃ hi₁ hi₂ hi₃ μ) A z
  have s2 := twistMulNormalForm_app ι e M₁ M₂ N₁ N₂ N₃ t₁ t₂ μ A x y
  have hu : ((restrictFunctorIsoPullback e).inv.app N₁).app A (t₁.app A x) = presheafMapW N₁ j (π₁ x) :=
    (congrArg (fun q => ((restrictFunctorIsoPullback e).inv.app N₁).app A q) (h₁ x)).trans
      (rFIPhomApp_inv_app_apply e inferInstance N₁ A _)
  have hv : ((restrictFunctorIsoPullback e).inv.app N₂).app A (t₂.app A y) = presheafMapW N₂ j (π₂ y) :=
    (congrArg (fun q => ((restrictFunctorIsoPullback e).inv.app N₂).app A q) (h₂ y)).trans
      (rFIPhomApp_inv_app_apply e inferInstance N₂ A _)
  rw [hu, hv, hμ] at s2
  have s3 := h₃ w
  have e0 : ∀ q, rFIPhomApp e inferInstance N₃ A q = ((restrictFunctorIsoPullback e).hom.app N₃).app A q :=
    fun _ => rfl
  have s4 : rFIPhomApp e inferInstance N₃ A (presheafMapW N₃ j (π₃ w)) =
      rFIPhomApp e inferInstance N₃ A (m (presheafMapW N₁ j (π₁ x)) (presheafMapW N₂ j (π₂ y))) :=
    s3.symm.trans (s1.trans (s2.trans (e0 _).symm))
  have s5 := rFIPhomApp_injective e inferInstance N₃ A s4
  have s6 : m (presheafMapW N₁ j (π₁ x)) (presheafMapW N₂ j (π₂ y)) = presheafMapW N₃ j (m' (π₁ x) (π₂ y)) := by
    rw [presheafMapW_def, presheafMapW_def, presheafMapW_def]
    exact (hm _ _).symm
  exact hj (s5.trans s6)


/-- A component `i.hom.app A` of an isomorphism of modules is injective. -/
theorem iso_hom_app_injective {M N : Y.Modules} (i : M ≅ N) (A : Y.Opens) :
    Function.Injective (i.hom.app A) := by
  intro p q hpq
  have k := fun v => ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ A) i.hom_inv_id) v
  simp only [Hom.comp_app, Hom.id_app, ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at k
  exact (k p).symm.trans ((congrArg (fun w => i.inv.app A w) hpq).trans (k q))

/-- If `f = g ∘ π` with `f` injective, then `π` is injective. -/
theorem injective_of_factor {α β γ : Type*} (f : α → β) (g : γ → β) (π : α → γ) (h : ∀ v, f v = g (π v))
    (hf : Function.Injective f) : Function.Injective π := by
  intro p q hpq
  exact hf ((h p).trans ((congrArg g hpq).trans (h q).symm))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Restriction of sections of `O(m)` is restriction of localization-valued functions, so it commutes
with the pointwise product `twistSectionMul`. -/
theorem twist_map_twistSectionMul (a b : ℤ) {U V : Opens (ProjectiveSpectrum.top 𝒜)} (i : V ⟶ U)
    (s : (MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 a).obj (op U))
    (t : (MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 b).obj (op U)) :
    (AlgebraicGeometry.Proj.twist 𝒜 (a + b)).presheaf.map i.op (twistSectionMul 𝒜 a b U s t) =
      twistSectionMul 𝒜 a b V ((AlgebraicGeometry.Proj.twist 𝒜 a).presheaf.map i.op s)
        ((AlgebraicGeometry.Proj.twist 𝒜 b).presheaf.map i.op t) := rfl

/-- `twistMul = L(twistMulPresheaf) ≫ ε` (Mathlib `Adjunction.homEquiv_counit`). -/
theorem twistMul_eq_map_comp_counit (a b : ℤ) :
    AlgebraicGeometry.Proj.twistMul 𝒜 a b =
      (AlgebraicGeometry.Scheme.Modules.shL (AlgebraicGeometry.Proj 𝒜)).map (twistMulPresheaf 𝒜 a b) ≫
        (AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Proj 𝒜)).counit.app
          (AlgebraicGeometry.Proj.twist 𝒜 (a + b)) :=
  Adjunction.homEquiv_counit _ _ _ _

/-- `twistMul` on the image of a pure tensor `s ⊗ t` under the sheafification unit (of
`moduleTensorPresheaf`) is the pointwise product `twistSectionMul`. -/
theorem twistMul_val_app_unit_tmul (a b : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (s : (MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 a).obj (op U))
    (t : (MiyaokaMori.WeightedJets.ProjTwisting.presheaf 𝒜 b).obj (op U)) :
    (AlgebraicGeometry.Proj.twistMul 𝒜 a b).val.app (op U)
        (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Proj 𝒜)).unit.app
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf (AlgebraicGeometry.Proj.twist 𝒜 a) (AlgebraicGeometry.Proj.twist 𝒜 b))).app
          (op U) (TensorProduct.tmul _ s t)) =
      twistSectionMul 𝒜 a b U s t := by
  refine (congrArg (fun k : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Proj.twist 𝒜 a)
      (AlgebraicGeometry.Proj.twist 𝒜 b) ⟶ AlgebraicGeometry.Proj.twist 𝒜 (a + b) => k.val.app (op U)
        (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Proj 𝒜)).unit.app
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf (AlgebraicGeometry.Proj.twist 𝒜 a) (AlgebraicGeometry.Proj.twist 𝒜 b))).app
          (op U) (TensorProduct.tmul _ s t))) (twistMul_eq_map_comp_counit 𝒜 a b)).trans ?_
  exact AlgebraicGeometry.Scheme.Modules.sheafify_unit_counit_eval (twistMulPresheaf 𝒜 a b) U
    (TensorProduct.tmul _ s t)

variable {τ B : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]

/-- The transition map θ is pointwise a ring homomorphism (`Localization.localRingHom`), hence multiplicative
on sections: θ(s·t) = θ(s)·θ(t). -/
theorem twistPushTransition_app_twistSectionMul (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (a b : ℤ)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB)
    (U : Y.Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 a (ιA ⁻¹ᵁ U))
    (t : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 b (ιA ⁻¹ᵁ U)) :
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ (a + b) (ιB ⁻¹ᵁ U) from
      ((twistPushTransition f hf (a + b) ιA ιB w).app U).hom (twistSectionMul 𝒜 a b (ιA ⁻¹ᵁ U) s t)) =
      twistSectionMul ℬ a b (ιB ⁻¹ᵁ U)
        (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ a (ιB ⁻¹ᵁ U) from
          ((twistPushTransition f hf a ιA ιB w).app U).hom s)
        (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ b (ιB ⁻¹ᵁ U) from
          ((twistPushTransition f hf b ιA ιB w).app U).hom t) := by
  refine Subtype.ext (funext fun y => ?_)
  have hy : ProjectiveSpectrum.comap f hf y.1 ∈ (ιA ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens) := by
    subst w; exact y.2
  refine (twistPushTransition_app_apply f hf (a + b) ιA ιB w U _ y hy).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun p q => p * q)
    (twistPushTransition_app_apply f hf a ιA ιB w U s y hy)
    (twistPushTransition_app_apply f hf b ιA ιB w U t y hy)).symm
  exact map_mul _ _ _

end AlgebraicGeometry.Proj

end
