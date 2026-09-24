import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoEvaluationUnit

/-! # Comparison of the unit map with `κ` on an affine chart

**Comparison on an affine chart** (the relative part of `isIso_pullback_one_evaluation_zero`): for `V ⊆ X` affine,
`e = affineIso S V : π⁻¹V ≅ Proj A(V)` and `ι : π⁻¹V ↪ Proj_X S`, after composing with the comparison isomorphism of
unit sheaves `unitRestrictIso` (`e^*𝟙 ≅ (π^*𝟙_X)|_{π⁻¹V}`) and with the `twistAffineIso` of Stacks 01NR
(`O(0)|_{π⁻¹V} ≅ e^*O_{Proj A(V)}(0)`), the restriction of `π^*𝟙_X → π^*S_0 → O(0)` to `π⁻¹V` is the pullback along
`e` of the canonical map `κ : 𝟙 → O(0)` on the absolute `Proj A(V)` (`TwistPowerIsoProjTwistZero`).

Sources: the construction of the evaluation map (`evaluation` is the adjoint transpose of `evaluationLocal` extended
from the affine basis, `evaluationLocal_eq`); Stacks 01MN (`twistSection`: `a ↦ a/1`), 01NR (`twistAffineIso`);
Mathlib's `SheafOfModules.pullbackObjUnitToUnit`.

Structure of the proof: after composing on the left with the isomorphism `(pullbackUnitIso e).inv`, both sides are
morphisms out of the unit sheaf and are determined by the image of `1` (`hom_ext_unit_of_eq_top`); on
`U₀ = e⁻¹ᵁ⊤` (`= ⊤`, `preimage_top` is `rfl`) both images of `1` compute to `unitEvalSection` (the pullback of
`twistSection 1` along the adjunction unit).

Remark on the style: everything is written in term style with `congrArg`/`Eq.trans`, one lemma per step with a
heartbeat limit — on goals containing both spellings `T.restrict ι` and `T` the motive of `rw` is ill-typed, and the
unifier, faced with `Hom.app (φ.inv ≫ φ.hom)`, would unfold the fourfold composite of `twistAffineIso` and time out
(hence `hom_app_inv_app` is stated for a **variable** `φ` and instantiated afterwards).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `hom.app ∘ inv.app = id` for an isomorphism (on sections; `φ` is a variable, so the unifier does not unfold a
concrete isomorphism). -/
theorem AlgebraicGeometry.Scheme.Modules.hom_app_inv_app {Y : AlgebraicGeometry.Scheme.{u}} {M N : Y.Modules}
    (φ : M ≅ N) (U : Y.Opens) (x : Γ(N, U)) : φ.hom.app U (φ.inv.app U x) = x :=
  congrArg (fun k : N ⟶ N => AlgebraicGeometry.Scheme.Modules.Hom.app k U x) φ.inv_hom_id

/-- Restricting twice is restricting once. -/
theorem AlgebraicGeometry.Scheme.Modules.map_map_res'' {Y : AlgebraicGeometry.Scheme.{u}} {M : Y.Modules}
    {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op x) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (V : X.affineOpens)

/-- The comparison isomorphism of unit sheaves `e^*𝟙_{Proj A(V)} ≅ (π^*𝟙_X)|_{π⁻¹V}`: `e^*𝟙 ≅ 𝟙_{π⁻¹V}`
(`pullbackUnitIso e`) `≅ 𝟙_P|_{π⁻¹V}` (the inverse of Mathlib's `restrictUnitIso`, with components the ring
isomorphisms `appIso`) `≅ (π^*𝟙_X)|_{π⁻¹V}` (the restriction functor applied to the inverse of `pullbackUnitIso π`). -/
noncomputable def unitRestrictIso :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).obj (SheafOfModules.unit (AlgebraicGeometry.Proj (S.sectionsGrading V.1)).ringCatSheaf) ≅
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj (SheafOfModules.unit X.ringCatSheaf)).restrict ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι :=
  (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom) ≪≫ (AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).symm ≪≫
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).mapIso (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom)).symm

/-- `t₁`: the global section `twistSection 1 = 1/1` (`= κ.app ⊤ 1`) of the absolute `Proj A(V)`, pulled back along the
adjunction unit to a section of `e^*O(0)` over `e⁻¹ᵁ⊤`. -/
noncomputable def unitEvalSection : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).obj (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) 0), ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).unit.app (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) 0)).app ⊤
    (AlgebraicGeometry.Proj.twistSection (S.sectionsGrading V.1) 1 (SetLike.one_mem_graded (S.sectionsGrading V.1)))

/-- ι ''ᵁ (e⁻¹ᵁ⊤) ≤ π⁻¹V (`ι ''ᵁ ⊤ = π⁻¹V`). -/
theorem image_preimage_top_le : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 :=
  (AlgebraicGeometry.Scheme.Opens.ι_image_top _).le

/-- Right-hand side: `e^*κ` applied to the "pulled-back `1`" is `unitEvalSection` (`pullbackUnitIso_inv_app_app`,
naturality of the adjunction unit, and `κ.app ⊤ 1 = twistSection 1`). -/
theorem unitRestrictEval_right :
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).map (AlgebraicGeometry.Proj.unitToTwistZero (S.sectionsGrading V.1))).app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)
        (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).inv ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)))) = (AlgebraicGeometry.Scheme.relativeProj.unitEvalSection S V) := by
  have h1 := AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_inv_app_app (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⊤ (1 : Γ(AlgebraicGeometry.Proj (S.sectionsGrading V.1), ⊤))
  rw [map_one] at h1
  refine (congrArg (fun y => ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).map (AlgebraicGeometry.Proj.unitToTwistZero (S.sectionsGrading V.1))).app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) y) h1).trans ?_
  refine (AlgebraicGeometry.Scheme.Modules.pullback_map_app_unit_app (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom (AlgebraicGeometry.Proj.unitToTwistZero (S.sectionsGrading V.1)) ⊤ (1 : Γ(AlgebraicGeometry.Proj (S.sectionsGrading V.1), ⊤))).trans ?_
  exact congrArg (fun y => ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).unit.app (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) 0)).app ⊤ y)
    (AlgebraicGeometry.Proj.unitToTwistZero_app_top_one (S.sectionsGrading V.1))

/-- `θ = π^*𝟙_X → π^*S_0 → O(0)` on `π⁻¹V`, applied to the "pulled-back `1`", equals
`evaluationLocal S 0 V (S.one.app V 1)`, i.e. the restriction of `twistAffineIso⁻¹ unitEvalSection` (adjoint transpose,
`evaluationPresheafHom_app_affine` and `evaluationLocal_eq`). -/
theorem unitRestrictEval_theta :
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))) =
      (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V)).op ((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (AlgebraicGeometry.Scheme.relativeProj.unitEvalSection S V)) := by
  have h2 := AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_inv_app_app (AlgebraicGeometry.Scheme.relativeProj S).hom V.1 (1 : Γ(X, V.1))
  rw [map_one] at h2
  have h3 : ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Scheme.relativeProj S).hom).unit.app (SheafOfModules.unit X.ringCatSheaf)).app V.1 (1 : Γ(X, V.1))) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 V (S.one.app V.1 (1 : Γ(X, V.1))) := by
    have e1 : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Scheme.relativeProj S).hom).homEquiv _ _ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0)).app V.1 (1 : Γ(X, V.1)) =
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Scheme.relativeProj S).hom).unit.app (SheafOfModules.unit X.ringCatSheaf)).app V.1 (1 : Γ(X, V.1))) := by
      rw [Adjunction.homEquiv_unit]
      rfl
    rw [← e1, Adjunction.homEquiv_naturality_left,
      AlgebraicGeometry.Scheme.relativeProj.homEquiv_evaluation]
    exact congrArg (fun k => k (S.one.app V.1 (1 : Γ(X, V.1))))
      (AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom_app_affine S 0 V)
  have h4 : AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S 0 V (S.one.app V.1 (1 : Γ(X, V.1))) =
      (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V)).op ((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (AlgebraicGeometry.Scheme.relativeProj.unitEvalSection S V)) := by
    rw [AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq]
    exact congrArg (fun t => (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V)).op
      ((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).unit.app (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) 0)).app ⊤ t)))
      (AlgebraicGeometry.Proj.twistSection_congr _
        (AlgebraicGeometry.Scheme.relativeProj.sectionsOf_one_app_one S V.1) _)
  exact (congrArg (fun y => ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) y) h2).trans (h3.trans h4)

set_option maxHeartbeats 200000 in
/-- `(pullbackUnitIso e).hom ∘ .inv` is the identity on `1`. -/
theorem pullbackUnitIso_hom_app_inv_app_one :
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)))) = (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))) :=
  congrArg (fun k : (SheafOfModules.unit ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme.ringCatSheaf) ⟶ (SheafOfModules.unit ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme.ringCatSheaf) => AlgebraicGeometry.Scheme.Modules.Hom.app k ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)))) (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).inv_hom_id

set_option maxHeartbeats 200000 in
/-- The `1` of the structure sheaf restricted from `π⁻¹V` to `ι''ᵁU₀` is still `1`. -/
theorem one_eq_unit_map_one :
    (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))) = (AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit (AlgebraicGeometry.Scheme.relativeProj S).left.ringCatSheaf)).map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)) :=
  (_root_.PresheafOfModules.unit_map_one (AlgebraicGeometry.Scheme.relativeProj S).left.ringCatSheaf.obj (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op).symm

set_option maxHeartbeats 200000 in
/-- The pulled-back `1` on `ι''ᵁU₀` is the restriction of the one on `π⁻¹V`. -/
theorem pullbackUnitIso_inv_app_one_restrict :
    AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))) =
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
        (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))) :=
  (congrArg (fun y => AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) y) (one_eq_unit_map_one S V)).trans
    (AlgebraicGeometry.Scheme.Modules.app_map_res' (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)))

set_option maxHeartbeats 200000 in
/-- Restriction along `ι''ᵁU₀ ≤ π⁻¹V ≤ ι''ᵁU₀` is the identity. -/
theorem twist_map_self_eq (y : Γ((AlgebraicGeometry.Scheme.relativeProj.twist S 0), ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE ((AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V).trans (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V))).op y = y := by
  have e6 : (homOfLE ((AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V).trans (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V)) : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ⟶ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) = 𝟙 _ := rfl
  rw [e6, op_id, (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map_id]
  rfl

set_option maxHeartbeats 200000 in
/-- `θ` commutes with restriction (on the pulled-back `1`). -/
theorem theta_app_map_restrict :
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
        (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)))) =
    (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)))) :=
  AlgebraicGeometry.Scheme.Modules.app_map_res' ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0) (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V) _

set_option maxHeartbeats 200000 in
/-- Left-hand side, step 1: cancel `(pullbackUnitIso e).hom ∘ .inv`. -/
theorem unitRestrictEval_left₁ :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
      ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)))))))) =
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
      ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)))))) :=
  congrArg (fun y => (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
    (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) y)))) (pullbackUnitIso_hom_app_inv_app_one S V)

set_option maxHeartbeats 200000 in
/-- Left-hand side, step 2: the inverse of `restrictUnitIso` sends `1` to `1`. -/
theorem unitRestrictEval_left₂ :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
      ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)))))) =
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))))) :=
  congrArg (fun y => (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
    (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) y)))
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_one ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))

set_option maxHeartbeats 200000 in
/-- Left-hand side, step 3: move the pulled-back `1` to `π⁻¹V`. -/
theorem unitRestrictEval_left₃ :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))))) =
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
        (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))))) :=
  congrArg (fun y => (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) y))
    (pullbackUnitIso_inv_app_one_restrict S V)

set_option maxHeartbeats 200000 in
/-- Left-hand side, step 4: `θ` commutes with restriction. -/
theorem unitRestrictEval_left₄ :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj (SheafOfModules.unit X.ringCatSheaf)).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
        (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))))) =
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ((AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))))) :=
  congrArg (fun y => (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) y) (theta_app_map_restrict S V)

/-- Left-hand side, last step: by `unitRestrictEval_theta`, the two restrictions compose to the identity; then use
`hom ∘ inv = id` for `twistAffineIso`. -/
theorem unitRestrictEval_left₅ :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ((AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1))))) = (AlgebraicGeometry.Scheme.relativeProj.unitEvalSection S V) := by
  let z : Γ((AlgebraicGeometry.Scheme.relativeProj.twist S 0), ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) := (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (AlgebraicGeometry.Scheme.relativeProj.unitEvalSection S V)
  have hz : (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (1 : Γ((AlgebraicGeometry.Scheme.relativeProj S).left, (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)))) = z :=
    (congrArg (fun y => (AlgebraicGeometry.Scheme.relativeProj.twist S 0).presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V)).op y) (unitRestrictEval_theta S V)).trans
      ((AlgebraicGeometry.Scheme.Modules.map_map_res'' (M := (AlgebraicGeometry.Scheme.relativeProj.twist S 0)) (AlgebraicGeometry.Scheme.relativeProj.image_preimage_top_le S V) (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V) z).trans
        (twist_map_self_eq S V z))
  exact (congrArg (fun y => (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) y) hz).trans
    (AlgebraicGeometry.Scheme.Modules.hom_app_inv_app (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0) ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (AlgebraicGeometry.Scheme.relativeProj.unitEvalSection S V))

/-- Left-hand side: the component of `unitRestrictIso` sends `1` to `1`, and then `θ` and `twistAffineIso` give
`unitEvalSection`. -/
theorem unitRestrictEval_left :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)
      (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0).app (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
        (AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
          ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)
            ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).hom.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).inv.app ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) (1 : Γ(((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme, ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)))))))) = (AlgebraicGeometry.Scheme.relativeProj.unitEvalSection S V) :=
  ((unitRestrictEval_left₁ S V).trans (unitRestrictEval_left₂ S V)).trans
    ((unitRestrictEval_left₃ S V).trans ((unitRestrictEval_left₄ S V).trans (unitRestrictEval_left₅ S V)))

/-- **Comparison on an affine chart**:
`unitRestrictIso.hom ≫ (π^*𝟙_X → π^*S_0 → O(0))|_{π⁻¹V} ≫ twistAffineIso.hom = e^*κ`.
Proof: after composing on the left with the isomorphism `(pullbackUnitIso e).inv` both sides are morphisms out of the
unit sheaf (`Iso.cancel_iso_inv_left`); by `hom_ext_unit_of_eq_top` it suffices to compare the images of `1` on
`U₀ = e⁻¹ᵁ⊤ = ⊤`: the left-hand side computes to `unitEvalSection` (`unitRestrictEval_left`), and so does the
right-hand side (`unitRestrictEval_right`). -/
theorem unitRestrictIso_hom_comp_restrict_eval :
    (unitRestrictIso S V).hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι).map ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S 0) ≫ (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).map (AlgebraicGeometry.Proj.unitToTwistZero (S.sectionsGrading V.1)) := by
  refine (Iso.cancel_iso_inv_left (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom) _ _).mp ?_
  apply AlgebraicGeometry.Scheme.Modules.hom_ext_unit_of_eq_top _ _ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) rfl
  exact (unitRestrictEval_left S V).trans (unitRestrictEval_right S V).symm

end AlgebraicGeometry.Scheme.relativeProj

end
