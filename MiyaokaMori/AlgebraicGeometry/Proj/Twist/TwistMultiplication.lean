import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueConstruction
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01nr
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplicationLocalAgreeAux
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplicationChartFormula
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.TwistMultiplicationRestrictTensorSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulPointwise

/-! # Multiplication of twisting sheaves on a relative Proj

The multiplication `O(a) ⊗ O(b) → O(a+b)` of the twisting sheaves of a relative Proj (locally the
map `S_a ⊗ S_b → S_{a+b}` in the graded localization); and, on the split weighted projectivization
`Y^sp`, the map sending sections of `(O(q) ⊗ π^*Q_i)^{⊗e}` to sections of `O(qe) ⊗ π^*Q_i^{⊗e}`
(not an isomorphism in the weighted case). The paper uses the latter to view `x_{i,q}^{m/q}` as a
section of `O(m) ⊗ π^*Q_i^{⊗m/q}` (proof of Proposition 2.4).

The local multiplication `twistMulLocal` is defined as the constant `Modules.twistMulLocalShape …`
with atomic parameters (the same eight-factor composite, see its docstring; auxiliary modules
`TwistMultiplicationLocalAgreeAux`, `TwistMultiplicationChartFormula`). Its section formulas (A)/(A′)
and the agreement (E) of pure tensor sections under principal-open refinement are in this module;
`twistMulLocal_agree_of_le` follows from (E) and `restrict_tensor_hom_ext`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

/- `Modules.tensor` (`moduleTensor`: the presheaf tensor product, sheafified) is not definitionally
   equal to the `⊗` of the monoidal structure on `X.Modules`, only canonically isomorphic through
   `Modules.tensorIsoTensorObj`; whenever the monoidal operations `tensorHom`, `tensorμ`, … are
   needed below, we pass to `⊗` through this isomorphism and come back to `Modules.tensor`. -/

/-- `restrictSectionMap` and `sectionMapOfRestrictHom` are two names for the same definition
(definitional equality). -/
theorem AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom
    {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} {W : X.Opens}
    (φ : M.restrict W.ι ⟶ N.restrict W.ι) (V : X.Opens) (hV : V ≤ W) :
    AlgebraicGeometry.Scheme.Modules.restrictSectionMap φ V hV =
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom φ V hV := rfl

/-- The local multiplication of `twistMul` on the affine piece `π⁻¹U`: `π⁻¹U ≅ Proj A(U)` (Stacks
01NQ), `O(n)|_{π⁻¹U} ≅ φ_U^* O_{Proj A(U)}(n)` (Stacks 01NR); locally take `Proj.twistMul`
(Stacks 01MO), the tensor product commutes with pullback (Stacks 01CD, `pullbackTensorIsoOpen`),
and restriction agrees with pullback (`restrictFunctorIsoPullback`). It is a separate definition
so that the compatibility on overlaps `twistMulLocal_agree` can be stated.

The body is `Modules.twistMulLocalShape ι e (T a) (T b) (T (a+b)) O(a) O(b) O(a+b)
(twistAffineIso a) (twistAffineIso b) (twistAffineIso (a+b)) (Proj.twistMul a b)`, an eight-factor
composite with atomic parameters. This is for kernel performance: on two applications of a
projection function such as `≫` or `NatTrans.app` the kernel unfolds wholesale instead of
comparing arguments first, so comparing the unfolded composite with any equation lemma is very
slow; with a constant with atomic parameters, `twistMulLocal S a b U = twistMulLocalShape …` is a
one-step delta, and every equation about `twistMulLocal` is a first-order instance, via
`congrArg`, of a generic lemma about `twistMulLocalShape`. Since `twistMulLocalShape` is a
`@[reducible] def`, `unfold twistMulLocal; infer_instance` in `twistMulLocal_isIso`
(`TwistPowerIso`) still sees through it. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistMulLocal {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b : ℤ) (U : X.affineOpens) :
    AlgebraicGeometry.Scheme.Modules.restrict
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S a)
          (AlgebraicGeometry.Scheme.relativeProj.twist S b))
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ⟶
      AlgebraicGeometry.Scheme.Modules.restrict (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι :=
  AlgebraicGeometry.Scheme.Modules.twistMulLocalShape ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom
    (AlgebraicGeometry.Scheme.relativeProj.twist S a) (AlgebraicGeometry.Scheme.relativeProj.twist S b)
    (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) a) (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) b)
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) (a + b))
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U a) (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U b)
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U (a + b))
    (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b)

/-- If `W` is a principal open of `U` (`h : ∃ f, D(f) = W`, which is the unfolded order
`⟨W.1, W.2⟩ ≤ ⟨U.1, U.2⟩` of Mathlib's `AffineZariskiSite`), then `W ≤ U`. -/
theorem AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq {X : AlgebraicGeometry.Scheme.{u}}
    {W U : X.affineOpens} (h : ∃ f : Γ(X, U.1), X.basicOpen f = W.1) : W.1 ≤ U.1 := by
  obtain ⟨f, hf⟩ := h
  exact hf ▸ X.basicOpen_le f

/-- The principal-open case of the second half of Stacks 01NQ (`affineIso_restrict`): for
`W = D_U(f) ≤ U` (the order of `AffineZariskiSite`), `affineIso` is compatible with the open
inclusion `π⁻¹W ⊆ π⁻¹U`: `e_W⁻¹ ≫ (π⁻¹W ⊆ π⁻¹U) = Proj.map(S(U) → S(W)) ≫ e_U⁻¹` (the `Proj.map`
on the right is written as a morphism of `projFunctor`). Proof: after composing with the
monomorphism `ι_U`, both sides are the chart `projChart W` (`affineIso_inv_ι` and
`map_projChart`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_homOfLE {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (W U : X.affineOpens) (h : ∃ f : Γ(X, U.1), X.basicOpen f = W.1) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
        (AlgebraicGeometry.Scheme.relativeProj S).left.homOfLE
          ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
            (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h)) =
      S.toGradedAffineAlgebra.projFunctor.map (CategoryTheory.homOfLE
          (show @LE.le X.AffineZariskiSite _ ⟨W.1, W.2⟩ ⟨U.1, U.2⟩ from h)) ≫
        (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).inv := by
  have hAZ : @LE.le X.AffineZariskiSite _ ⟨W.1, W.2⟩ ⟨U.1, U.2⟩ := h
  refine (CategoryTheory.cancel_mono ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι).mp ?_
  refine (CategoryTheory.Category.assoc _ _ _).trans ?_
  refine (congrArg (CategoryTheory.CategoryStruct.comp
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv) (AlgebraicGeometry.Scheme.homOfLE_ι _ _)).trans ?_
  refine (AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S W).trans ?_
  refine (S.toGradedAffineAlgebra.map_projChart hAZ).symm.trans ?_
  refine (congrArg (CategoryTheory.CategoryStruct.comp
    (S.toGradedAffineAlgebra.projFunctor.map (CategoryTheory.homOfLE hAZ)))
    (AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S U).symm).trans ?_
  exact (CategoryTheory.Category.assoc _ _ _).symm

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- `twistMulLocal` is the shape constant applied to the chart data (one delta step). -/
theorem twistMulLocal_eq_shape (a b : ℤ) (U : X.affineOpens) :
    AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U =
      AlgebraicGeometry.Scheme.Modules.twistMulLocalShape ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι
        (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom
        (AlgebraicGeometry.Scheme.relativeProj.twist S a) (AlgebraicGeometry.Scheme.relativeProj.twist S b)
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) a) (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) b)
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) (a + b))
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U a)
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U b)
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U (a + b))
        (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b) := rfl

/-- **(A) Section formula for the local multiplication on a pure tensor section.** For `A ⊆ π⁻¹U` and sections
`x ∈ Γ(O(a), ι_U''A)`, `y ∈ Γ(O(b), ι_U''A)`, the chart section (`twistπ`) of
`twistMulLocal S a b U` applied to `η(x ⊗ y)` is the pointwise product (`twistSectionMul`) of the chart sections of
`x` and `y`. Instance of the generic engine `Modules.twistMulLocalShape_app_unit_tmul` with the section formula
`twistAffineHom_app_apply`, `Proj.twistMul_val_app_unit_tmul` and `Proj.twist_map_twistSectionMul`. -/
theorem twistπ_app_twistMulLocal_app_unit_tmul (a b : ℤ) (U : X.affineOpens)
    (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)))
    (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A))) :
    (S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app
        (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)
        ((AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U).app A
          (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
            ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
              (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
            (op (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)) (TensorProduct.tmul _ x y))) =
      AlgebraicGeometry.Proj.twistSectionMul (S.sectionsGrading U.1) a b
        (chartOpen S U (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A))
        ((S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app
          (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) x :
          (MiyaokaMori.WeightedJets.ProjTwisting.presheaf (S.sectionsGrading U.1) a).obj
            (op (chartOpen S U (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A))))
        ((S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app
          (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) y :
          (MiyaokaMori.WeightedJets.ProjTwisting.presheaf (S.sectionsGrading U.1) b).obj
            (op (chartOpen S U (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)))) := by
  have key := AlgebraicGeometry.Scheme.Modules.twistMulLocalShape_app_unit_tmul
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom
    (AlgebraicGeometry.Scheme.relativeProj.twist S a) (AlgebraicGeometry.Scheme.relativeProj.twist S b)
    (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) a) (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) b)
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) (a + b))
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U a) (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U b)
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S U (a + b))
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U a) (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U b)
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U (a + b))
    (twistAffineIso_hom S U a) (twistAffineIso_hom S U b) (twistAffineIso_hom S U (a + b))
    (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b) A
    (CategoryTheory.eqToHom (affineIso_image_eq_chartOpen S U A))
    (fun v => (S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) v)
    (fun v => (S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) v)
    (fun v => (S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) v)
    (twistAffineHom_app_apply S U a A) (twistAffineHom_app_apply S U b A) (twistAffineHom_app_apply S U (a + b) A)
    (AlgebraicGeometry.Proj.twistSectionMul (S.sectionsGrading U.1) a b _)
    (AlgebraicGeometry.Proj.twistSectionMul (S.sectionsGrading U.1) a b _)
    (AlgebraicGeometry.Proj.twistMul_val_app_unit_tmul (S.sectionsGrading U.1) a b _)
    (AlgebraicGeometry.Proj.twist_map_twistSectionMul (S.sectionsGrading U.1) a b _)
    (AlgebraicGeometry.Scheme.Modules.presheafMapW_eqToHom_injective _ _) x y
  exact (congrArg (fun k : AlgebraicGeometry.Scheme.Modules.restrict
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S a)
        (AlgebraicGeometry.Scheme.relativeProj.twist S b)) ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ⟶
      AlgebraicGeometry.Scheme.Modules.restrict (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι =>
    (S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app
    (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)
    (AlgebraicGeometry.Scheme.Modules.Hom.app k A
      (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
        ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
          (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
        (op (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)) (TensorProduct.tmul _ x y))))
    (twistMulLocal_eq_shape S a b U)).trans key

/-- **(A′) Section formula for the local multiplication, for an arbitrary open `B ≤ π⁻¹U`**, in terms of the
section map `restrictSectionMap` of `ModulesGlueConstruction`: write `B = ι_U''A` (`image_preimage_ι_eq`),
where `restrictSectionMap φ (ι_U''A) = φ.app A` (`sectionMapOfRestrictHom_image`), and apply (A). -/
theorem twistπ_app_restrictSectionMap_twistMulLocal_unit_tmul (a b : ℤ) (U : X.affineOpens)
    (B : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hB : B ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, B))
    (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, B)) :
    (S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app B
        (AlgebraicGeometry.Scheme.Modules.restrictSectionMap
          (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) B hB
          (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
            ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
              (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
            (op B) (TensorProduct.tmul _ x y))) =
      AlgebraicGeometry.Proj.twistSectionMul (S.sectionsGrading U.1) a b (chartOpen S U B)
        ((S.toGradedAffineAlgebra.twistπ a (AlgebraicGeometry.Scheme.affineSite U)).app B x :
          (MiyaokaMori.WeightedJets.ProjTwisting.presheaf (S.sectionsGrading U.1) a).obj (op (chartOpen S U B)))
        ((S.toGradedAffineAlgebra.twistπ b (AlgebraicGeometry.Scheme.affineSite U)).app B y :
          (MiyaokaMori.WeightedJets.ProjTwisting.presheaf (S.sectionsGrading U.1) b).obj (op (chartOpen S U B))) := by
  obtain ⟨A, rfl⟩ : ∃ A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens,
      B = ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A :=
    ⟨((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ B, (image_preimage_ι_eq S U B hB).symm⟩
  have h0 : AlgebraicGeometry.Scheme.Modules.restrictSectionMap
      (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U)
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) hB =
      (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U).app A :=
    (AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom _ _ hB).trans
      (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_image
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) A hB)
  have h1 := ConcreteCategory.congr_hom h0
    (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
      ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
        (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
      (op (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)) (TensorProduct.tmul _ x y))
  have h2 := twistπ_app_twistMulLocal_app_unit_tmul S a b U A x y
  exact (congrArg (fun w => (S.toGradedAffineAlgebra.twistπ (a + b) (AlgebraicGeometry.Scheme.affineSite U)).app
    (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) w) h1).trans h2

/-- **(E) Agreement of the local multiplications on pure tensor sections, along a principal affine refinement.**
`W = D_U(f) ≤ U` (the hypothesis `h` is the order of `AffineZariskiSite` unfolded), `B ≤ π⁻¹W`,
`x ∈ Γ(O(a), B)`, `y ∈ Γ(O(b), B)`; then the section maps of `twistMulLocal S a b W` and `twistMulLocal S a b U`
on `B` agree on `η(x ⊗ y)`. See the module docstring for the proof. -/
theorem restrictSectionMap_twistMulLocal_agree_of_le_unit_tmul (a b : ℤ) (W U : X.affineOpens)
    (h : ∃ f : Γ(X, U.1), X.basicOpen f = W.1) (B : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hB : B ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, B))
    (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, B)) :
    AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b W) B hB
        (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
          ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
            (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
          (op B) (TensorProduct.tmul _ x y)) =
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) B
        (hB.trans ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
          (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h)))
        (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
          ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
            (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
          (op B) (TensorProduct.tmul _ x y)) := by
  have hAZ : @LE.le X.AffineZariskiSite _ (AlgebraicGeometry.Scheme.affineSite W)
    (AlgebraicGeometry.Scheme.affineSite U) := h
  apply AlgebraicGeometry.Scheme.relativeProj.twistπ_app_injective S (a + b) W B hB
  have lhs := twistπ_app_restrictSectionMap_twistMulLocal_unit_tmul S a b W B hB x y
  have rhs := twistπ_app_restrictSectionMap_twistMulLocal_unit_tmul S a b U B
    (hB.trans ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
      (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h))) x y
  refine lhs.trans ?_
  refine Eq.trans ?_ (twistπ_app_eq_twistTransition_app S (a + b) hAZ B _).symm
  refine Eq.trans ?_ (congrArg (fun w => (S.toGradedAffineAlgebra.twistTransition (a + b) hAZ).app B w) rhs).symm
  refine (congrArg₂ (AlgebraicGeometry.Proj.twistSectionMul (S.sectionsGrading W.1) a b (chartOpen S W B))
    (twistπ_app_eq_twistTransition_app S a hAZ B x) (twistπ_app_eq_twistTransition_app S b hAZ B y)).trans ?_
  exact (twistTransition_app_twistSectionMul S a b hAZ B _ _).symm

end AlgebraicGeometry.Scheme.relativeProj

/-- The local multiplications agree under **principal-open refinement** (the core of the
multiplication part of Stacks 01NR): if `W = D_U(f) ≤ U` is a principal open of `U` (`h`, the
unfolded order `⟨W.1, W.2⟩ ≤ ⟨U.1, U.2⟩` of `AffineZariskiSite`) and `V ≤ π⁻¹W`, then
`twistMulLocal S a b W` and `twistMulLocal S a b U` give the same section map
`Γ(O(a) ⊗ O(b), V) ⟶ Γ(O(a+b), V)` on `V`.

Sources: Stacks 01NR (multiplication corresponds chart by chart), 01MX (pointwise description of
θ); Lemma 2.2 of the paper.

Proof:
1. Restrict `twistMulLocal S a b U` along `j : π⁻¹W ⊆ π⁻¹U` and transport it to `M|_{π⁻¹W}` with
   Mathlib's `restrictFunctorCongr` (`ι_W = j ≫ ι_U`) and `restrictFunctorComp`, obtaining
   `ψ′ : M|_{π⁻¹W} ⟶ N|_{π⁻¹W}`; its components are
   `M.presheaf.map (eqToHom _) ≫ (twistMulLocal U).app (j''A) ≫ N.presheaf.map (eqToHom _)` (the
   components of the two Mathlib isomorphisms are by definition restrictions of `eqToHom`), so
   `sectionMapOfRestrictHom_eq_of_app_eq` gives
   `restrictSectionMap ψ′ V = restrictSectionMap (twistMulLocal U) V`.
2. `twistMulLocal S a b W = ψ′`: by `restrict_tensor_hom_ext` it suffices to compare on pure tensor
   sections `η(x ⊗ y)` (`x`, `y` sections on `ι_W''A`); both sides are values of
   `restrictSectionMap` on `ι_W''A` (`sectionMapOfRestrictHom_image`), which reduces to
   `restrictSectionMap_twistMulLocal_agree_of_le_unit_tmul` ((E): compare through the injective
   chart section map `twistπ (a+b) W` — the chart sections of both pieces are pointwise products
   `twistSectionMul` ((A′)), related by the transition map θ (`twistπ_transition`, and θ is
   pointwise `Localization.localRingHom`)). -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_agree_of_le {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b : ℤ) (W U : X.affineOpens) (h : ∃ f : Γ(X, U.1), X.basicOpen f = W.1)
    (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hV : V ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1) :
    AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b W) V hV =
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) V
        (hV.trans ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
          (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h))) := by
  -- the open inclusion j : π⁻¹W ⊆ π⁻¹U and the transport ψ′ of the U-piece to π⁻¹W
  let j : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).toScheme ⟶
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme :=
    (AlgebraicGeometry.Scheme.relativeProj S).left.homOfLE
      ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
        (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h))
  have hcomp : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι =
      j ≫ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι :=
    (AlgebraicGeometry.Scheme.homOfLE_ι (AlgebraicGeometry.Scheme.relativeProj S).left
      ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
        (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h))).symm
  let ψ' : (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S a)
        (AlgebraicGeometry.Scheme.relativeProj.twist S b)).restrict
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ⟶
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b)).restrict
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr hcomp).hom.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorComp j
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι).hom.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).map
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorComp j
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι).inv.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr hcomp).inv.app _
  have h3g : ∀ {M' N' : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Modules} (φ : M' ⟶ N')
      (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).toScheme.Opens),
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor j).map φ).app A = φ.app (j ''ᵁ A) := fun _ _ => rfl
  have hψ' : ∀ A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).toScheme.Opens, ψ'.app A =
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S a)
        (AlgebraicGeometry.Scheme.relativeProj.twist S b)).presheaf.map (CategoryTheory.eqToHom
          (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image
            ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
              (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h)) A)).op ≫
      (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U).app (j ''ᵁ A) ≫
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b)).presheaf.map (CategoryTheory.eqToHom
        (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image
          ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
            (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h)) A).symm).op := by
    intro A
    simp only [ψ', AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
      AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_hom_app_app,
      AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_hom_app_app,
      AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_inv_app_app,
      AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_inv_app_app, h3g]
    erw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.op_comp, CategoryTheory.eqToHom_trans,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp, CategoryTheory.eqToHom_trans]
    rfl
  -- the W-piece equals the transported U-piece: both are determined by pure tensor sections
  have key : AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b W = ψ' := by
    refine AlgebraicGeometry.Scheme.Modules.restrict_tensor_hom_ext
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι
      (AlgebraicGeometry.Scheme.relativeProj.twist S a) (AlgebraicGeometry.Scheme.relativeProj.twist S b) _ _
      (fun A x y => ?_)
    have hA : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ''ᵁ A ≤
        (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1 := by
      conv_rhs => rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)]
      exact AlgebraicGeometry.Scheme.Hom.image_le_opensRange _ _
    -- e1 : restrictSectionMap (twistMulLocal W) (ι_W''A) = (twistMulLocal W).app A
    have e1 := ConcreteCategory.congr_hom
      ((AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom
          (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b W) _ hA).trans
        (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_image
          (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b W) A hA))
      (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
        ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
          (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
        (op (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ''ᵁ A)) (TensorProduct.tmul _ x y))
    -- e2 : restrictSectionMap ψ' (ι_W''A) = ψ'.app A
    have e2 := ConcreteCategory.congr_hom
      ((AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom ψ' _ hA).trans
        (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_image ψ' A hA))
      (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
        ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
          (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
        (op (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ''ᵁ A)) (TensorProduct.tmul _ x y))
    -- e3 : restrictSectionMap ψ' (ι_W''A) = restrictSectionMap (twistMulLocal U) (ι_W''A)
    have e3 := ConcreteCategory.congr_hom
      ((AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom ψ' _ hA).trans
        ((AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_eq_of_app_eq
            ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
              (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h))
            (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) ψ' hψ' _ hA).trans
          (AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom
            (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) _ _).symm))
      (((AlgebraicGeometry.Scheme.Modules.shAdj (AlgebraicGeometry.Scheme.relativeProj S).left).unit.app
        ((AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S a) ⊗
          (AlgebraicGeometry.Scheme.Modules.shG _).obj (AlgebraicGeometry.Scheme.relativeProj.twist S b))).app
        (op (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ''ᵁ A)) (TensorProduct.tmul _ x y))
    -- e4 : (E) on the pure tensor section
    have e4 := AlgebraicGeometry.Scheme.relativeProj.restrictSectionMap_twistMulLocal_agree_of_le_unit_tmul S a b W U h
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ''ᵁ A) hA x y
    exact e1.symm.trans (e4.trans (e3.symm.trans e2))
  rw [key]
  exact (AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom ψ' V hV).trans
    ((AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_eq_of_app_eq
        ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono
          (AlgebraicGeometry.Scheme.affineOpens.le_of_basicOpen_eq h))
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) ψ' hψ' V hV).trans
      (AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) V _).symm)

/-- The local multiplications agree on overlaps: for affine opens `U`, `U′` and
`V ≤ π⁻¹U ⊓ π⁻¹U′`, the section maps `Γ(O(a) ⊗ O(b), V) ⟶ Γ(O(a+b), V)` given by `twistMulLocal`
on `U` and on `U′` coincide. This is the compatibility hypothesis of `glueHom`.
Proof (reduction to the principal-open case `twistMulLocal_agree_of_le`):
1. `O(a+b)` is a sheaf, so equality of section maps is local (`TopCat.Sheaf.eq_of_locally_eq'`):
   `V` is covered by the `V ⊓ π⁻¹D`, where `D` runs over the opens that are principal in both `U`
   and `U′`, `D = D_U(f) = D_{U′}(g)` (Mathlib's `exists_basicOpen_le_affine_inter`: the
   intersection of affine opens `U`, `U′` is covered by such `D`);
2. the section maps are natural in `V` (`sectionMapOfRestrictHom_nat`), so it suffices to compare
   on each piece `V ⊓ π⁻¹D`;
3. on `V ⊓ π⁻¹D ≤ π⁻¹D`, the section maps of the `U`-piece and of the `U′`-piece both equal that of
   the `D`-piece (`twistMulLocal_agree_of_le`; `D ≤ U` and `D ≤ U′` are both instances of the order
   of `AffineZariskiSite`), hence they agree. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_agree {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b : ℤ) (U U' : X.affineOpens)
    (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hU : V ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
    (hU' : V ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U'.1) :
    AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) V hU =
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U') V hU' := by
  let π := (AlgebraicGeometry.Scheme.relativeProj S).hom
  let N := AlgebraicGeometry.Scheme.relativeProj.twist S (a + b)
  let J := { p : Γ(X, U.1) × Γ(X, U'.1) // X.basicOpen p.1 = X.basicOpen p.2 }
  let Vi : J → (AlgebraicGeometry.Scheme.relativeProj S).left.Opens :=
    fun p => V ⊓ π ⁻¹ᵁ X.basicOpen p.1.1
  ext s
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ Vi V
    (fun i => CategoryTheory.homOfLE inf_le_left) ?_ _ _ ?_
  · intro x hx
    obtain ⟨f, g, hfg, hxf⟩ := AlgebraicGeometry.exists_basicOpen_le_affine_inter U.2 U'.2 (π x)
      ⟨hU hx, hU' hx⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(f, g), hfg⟩, hx, hxf⟩
  · intro i
    have e1 := ConcreteCategory.congr_hom (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_nat
      (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) V (Vi i) hU inf_le_left) s
    have e2 := ConcreteCategory.congr_hom (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_nat
      (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U') V (Vi i) hU' inf_le_left) s
    simp only [ConcreteCategory.comp_apply] at e1 e2
    change N.presheaf.map _ (AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) V hU s) =
      N.presheaf.map _ (AlgebraicGeometry.Scheme.Modules.restrictSectionMap
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U') V hU' s)
    rw [AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom,
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap_eq_sectionMapOfRestrictHom, ← e1, ← e2]
    let D : X.affineOpens := ⟨X.basicOpen i.1.1, U.2.basicOpen i.1.1⟩
    have hDU : ∃ f : Γ(X, U.1), X.basicOpen f = D.1 := ⟨i.1.1, rfl⟩
    have hDU' : ∃ g : Γ(X, U'.1), X.basicOpen g = D.1 := ⟨i.1.2, i.2.symm⟩
    have hVi : Vi i ≤ π ⁻¹ᵁ D.1 := inf_le_right
    have k1 := AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_agree_of_le S a b D U hDU (Vi i) hVi
    have k2 := AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_agree_of_le S a b D U' hDU' (Vi i) hVi
    have key : AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) (Vi i) (inf_le_left.trans hU) =
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U') (Vi i) (inf_le_left.trans hU') :=
      k1.symm.trans k2
    exact ConcreteCategory.congr_hom key _

/-- The multiplication `O(a) ⊗ O(b) ⟶ O(a+b)` of the twisting sheaves of a relative Proj: the local
multiplications `twistMulLocal` on the affine pieces are glued along the cover `{π⁻¹U}`. `glueHom`
glues constructively with Mathlib's `restrictHomEquivHom` (no choice), taking as hypothesis that
the pieces agree on overlaps (`twistMulLocal_agree`: the comparison isomorphisms of Stacks 01NO
commute with the graded multiplication). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistMul {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b : ℤ) :
    AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S a)
        (AlgebraicGeometry.Scheme.relativeProj.twist S b) ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S (a + b) :=
  let π := (AlgebraicGeometry.Scheme.relativeProj S).hom
  let T := AlgebraicGeometry.Scheme.relativeProj.twist S
  AlgebraicGeometry.Scheme.Modules.glueHom (fun U : X.affineOpens => π ⁻¹ᵁ U.1)
    (by rw [← AlgebraicGeometry.Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top,
      AlgebraicGeometry.Scheme.Hom.preimage_top])
    (AlgebraicGeometry.Scheme.Modules.tensor (T a) (T b)) (T (a + b))
    (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b)
    (fun U U' V hU hU' => AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_agree S a b U U' V hU hU')

/-- On `Y^sp`: the map `(O(q) ⊗ π^*Q)^{⊗e} → O(qe) ⊗ π^*(Q^{⊗e})`, built by recursion on `e`
following `tensorPow` (with `τ := Modules.tensorIsoTensorObj`):
* `e = 0`: `O = O ⊗ O → O(0) ⊗ π^*O` (`O → π^*S_0 → O(0)` is the evaluation `1 ↦ 1`, and
  `π^*O ≅ O`), then back to `Modules.tensor` through `τ⁻¹`;
* `e + 1`: pass to `⊗` through `τ`, use `Ψ_e` and the `tensorμ` of the symmetric monoidal
  structure to rearrange into `(O(qe) ⊗ O(q)) ⊗ (π^*Q^{⊗e} ⊗ π^*Q)`, apply `twistMul` and the
  inverse of `pullbackTensorIso`, transport the index `qe + q = q(e+1)` by `eqToHom`, and return
  to `Modules.tensor` through `τ⁻¹`.
`splitTwistMul` takes `e = m/q`, transports the index `q(m/q) = m` (`q ∣ m`), and acts on global
sections. -/
noncomputable def splitTwistMul {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (kk : ℕ)
    (i : Fin (n + 1)) (q m : ℕ) (hqm : q ∣ m) :
    ((AlgebraicGeometry.Scheme.Modules.tensorPow
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (q : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
            (F.lineQuotient i).toModules)) (m / q)).val.obj (Opposite.op ⊤) : Type u) →
      ((AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q)))).val.obj
          (Opposite.op ⊤) : Type u) :=
  let S := splitWeightedAlgebraOf F kk
  let Y := (splitWeightedProjectivization F kk).left
  let π := (splitWeightedProjectivization F kk).hom
  let T := AlgebraicGeometry.Scheme.relativeProj.twist S
  let Q := (F.lineQuotient i).toModules
  let τ := fun A B : Y.Modules => AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B
  let Ψ : ∀ e : ℕ,
      AlgebraicGeometry.Scheme.Modules.tensorPow
          (AlgebraicGeometry.Scheme.Modules.tensor (T (q : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)) e ⟶
        AlgebraicGeometry.Scheme.Modules.tensor (T ((q * e : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)) := fun e =>
    Nat.rec (motive := fun e =>
        AlgebraicGeometry.Scheme.Modules.tensorPow
            (AlgebraicGeometry.Scheme.Modules.tensor (T (q : ℤ))
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)) e ⟶
          AlgebraicGeometry.Scheme.Modules.tensor (T ((q * e : ℕ) : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
              (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)))
      ((CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := Y.Modules)
          (SheafOfModules.unit _)).inv ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules)
          ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso π).inv ≫
            (AlgebraicGeometry.Scheme.Modules.pullback π).map S.one ≫
            AlgebraicGeometry.Scheme.relativeProj.evaluation S 0)
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso π).inv ≫
        (τ _ _).inv)
      (fun e Ψe =>
        (τ _ _).hom ≫
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules) (Ψe ≫ (τ _ _).hom) (τ _ _).hom ≫
          CategoryTheory.MonoidalCategory.tensorμ (C := Y.Modules) _ _ _ _ ≫
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules)
            ((τ _ _).inv ≫ AlgebraicGeometry.Scheme.relativeProj.twistMul S _ _ ≫
              CategoryTheory.eqToHom (congrArg T (by push_cast; ring)))
            ((τ _ _).inv ≫ (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π _ _).inv) ≫
          (τ _ _).inv)
      e
  fun x =>
    ((Ψ (m / q) ≫ CategoryTheory.eqToHom (congrArg
        (fun k : ℤ => AlgebraicGeometry.Scheme.Modules.tensor (T k)
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q (m / q))))
        (by rw [Nat.mul_div_cancel' hqm]))).val.app (Opposite.op ⊤)).hom x


end
