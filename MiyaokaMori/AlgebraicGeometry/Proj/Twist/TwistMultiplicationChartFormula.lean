import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01nr
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplicationChartSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplicationLocalAgreeAux
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLimit
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition

/-! # Chart section formulas of the relative Proj

Facts about the charts `π⁻¹U ≅ Proj S(U)` (Stacks 01NQ/01NR) used by `relativeProj.twistMulLocal_agree_of_le`
(module `TwistMultiplication`); nothing here mentions `twistMulLocal`.

* `chartOpen S U B` — the chart open `c_U⁻¹B`, typed in the world of `S.sectionsGrading U.1` (see its docstring for why
  the two definitionally equal gradings must not be mixed inside one application).
* `twistAffineHom_app'` / `twistAffineHom_app_apply` — the section formula for the 01NR comparison map
  `twistAffineHom S U n`, spelled with its own codomain `Proj.twist (S.sectionsGrading U.1) n` (the variant
  `twistAffineHom_app` of `TwistMultiplicationChartSections` uses `chartTwist`).
* `twistπ_app_eq_twistTransition_app` — `twistπ_transition` pointwise: for a principal affine refinement `W ≤ U`,
  the chart section on `W` is the transition map θ (Stacks 01MX) of the chart section on `U`.
* `twistTransition_app_twistSectionMul` — θ is multiplicative on sections (pointwise it is the ring homomorphism
  `Localization.localRingHom`; module `ProjTwistPushTransition`).

Sources: Stacks 01NR (multiplication corresponds chart by chart), 01MX (pointwise description of θ);
Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- The chart open `c_U⁻¹ B ⊆ Proj S(U)`, **typed in the world of `S.sectionsGrading U.1`** (the codomain of
`affineIso S U`, used by `twistAffineHom`, `twistMulLocal`, `Proj.twistMul`). The chart `chartMap S U` itself lives over
`S.toGradedAffineAlgebra.grading (affineSite U)`; the two gradings are definitionally equal but carry syntactically
different `CommRing`/`GradedRing` instance terms, and unifying an open of one world into an application of the other
makes instance synthesis fail (`GradedRing (S.sectionsGrading U.1)` "not found"). Wrapping the open in this regular
definition keeps every application inside one world; crossing happens only at the level of sections. -/
def chartOpen (U : X.affineOpens) (B : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens) :
    (AlgebraicGeometry.Proj (S.sectionsGrading U.1)).Opens :=
  AlgebraicGeometry.Scheme.relativeProj.chartMap S U ⁻¹ᵁ B

/-- `e_U ''ᵁ A = chartOpen S U (ι_U ''ᵁ A)` (`affineIso_image_eq_chartMap_preimage`, retyped). -/
theorem affineIso_image_eq_chartOpen (U : X.affineOpens)
    (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom ''ᵁ A =
      chartOpen S U (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) :=
  AlgebraicGeometry.Scheme.relativeProj.affineIso_image_eq_chartMap_preimage S U A

/-- **Section formula for `twistAffineHom`** (01NR comparison map), spelled with the codomain
`Proj.twist (S.sectionsGrading U.1) n` of `twistAffineHom` itself (the variant `twistAffineHom_app` of
`TwistMultiplicationChartSections` uses `chartTwist`): on `A ⊆ π⁻¹U`,
`(twistAffineHom S U n).app A = twistπ.app (ι_U''A) ≫ (transport along e_U''A = c_U⁻¹(ι_U''A)) ≫ (rFIP e_U).hom`.
Same proof as `twistAffineHom_app`: all data of `chart_comparison_app_noE` are unified from the unfolded body. -/
theorem twistAffineHom_app' (U : X.affineOpens) (n : ℤ)
    (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens) :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U n).app A =
      (S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)).app
          (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) ≫
        AlgebraicGeometry.Scheme.Modules.presheafMapW (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n)
          (CategoryTheory.eqToHom
            (AlgebraicGeometry.Scheme.relativeProj.affineIso_image_eq_chartMap_preimage S U A)) ≫
        AlgebraicGeometry.Scheme.Modules.rFIPhomApp (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom
          inferInstance (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n) A := by
  unfold AlgebraicGeometry.Scheme.relativeProj.twistAffineHom
  dsimp only
  refine AlgebraicGeometry.Scheme.Modules.chart_comparison_app_noE _ _ _ _ _ ?_ _ _ _ _ _ ?_ A _
  · exact S.toGradedAffineAlgebra.projChart_isOpenImmersion _
  · exact AlgebraicGeometry.Scheme.GradedAffineAlgebra.twistChartHom_eq S.toGradedAffineAlgebra n _

/-- Pointwise form of `twistAffineHom_app'`. -/
theorem twistAffineHom_app_apply (U : X.affineOpens) (n : ℤ)
    (A : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens)
    (v : Γ((AlgebraicGeometry.Scheme.relativeProj.twist S n).restrict ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι, A)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U n).app A v =
      AlgebraicGeometry.Scheme.Modules.rFIPhomApp (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom
        inferInstance (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n) A
        (AlgebraicGeometry.Scheme.Modules.presheafMapW (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n)
          (CategoryTheory.eqToHom
            (AlgebraicGeometry.Scheme.relativeProj.affineIso_image_eq_chartMap_preimage S U A))
          ((S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)).app
            (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) v)) := by
  have h1 := ConcreteCategory.congr_hom (twistAffineHom_app' S U n A) v
  refine h1.trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  exact ConcreteCategory.comp_apply _ _ _

/-- `ι_U ''ᵁ (ι_U ⁻¹ᵁ B) = B` for `B ≤ π⁻¹U`. -/
theorem image_preimage_ι_eq (U : X.affineOpens) (B : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (hB : B ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) :
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ⁻¹ᵁ B) = B := by
  rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf, AlgebraicGeometry.Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hB

/-- The transition map `twistTransition` (θ of Stacks 01MX, between the charts `U ≥ W` of the relative Proj) is
multiplicative on sections: relativeProj-level form of `Proj.twistPushTransition_app_twistSectionMul`
(`twistTransition m h` is by definition `twistPushTransition (restrictGraded h) …`). -/
theorem twistTransition_app_twistSectionMul (a b : ℤ) {W U : X.AffineZariskiSite} (h : W ≤ U)
    (B : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading U) a
      (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ B))
    (t : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading U) b
      (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ B)) :
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W) (a + b)
        (S.toGradedAffineAlgebra.projChart W ⁻¹ᵁ B) from
      ((S.toGradedAffineAlgebra.twistTransition (a + b) h).app B).hom
        (AlgebraicGeometry.Proj.twistSectionMul (S.toGradedAffineAlgebra.grading U) a b
          (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ B) s t)) =
      AlgebraicGeometry.Proj.twistSectionMul (S.toGradedAffineAlgebra.grading W) a b
        (S.toGradedAffineAlgebra.projChart W ⁻¹ᵁ B)
        (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W) a
            (S.toGradedAffineAlgebra.projChart W ⁻¹ᵁ B) from
          ((S.toGradedAffineAlgebra.twistTransition a h).app B).hom s)
        (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W) b
            (S.toGradedAffineAlgebra.projChart W ⁻¹ᵁ B) from
          ((S.toGradedAffineAlgebra.twistTransition b h).app B).hom t) :=
  AlgebraicGeometry.Proj.twistPushTransition_app_twistSectionMul (S.toGradedAffineAlgebra.grading U)
    (S.toGradedAffineAlgebra.restrictGraded h)
    (S.toGradedAffineAlgebra.restrict_irrelevant_le h) a b (S.toGradedAffineAlgebra.projChart U)
    (S.toGradedAffineAlgebra.projChart W) (S.toGradedAffineAlgebra.map_projChart h) B s t

/-- `twistπ_transition` pointwise: for `W ≤ U` in `AffineZariskiSite` and `z ∈ Γ(O(n), B)`,
`twistπ n W (z) = θ (twistπ n U (z))`. -/
theorem twistπ_app_eq_twistTransition_app (n : ℤ) {W U : X.AffineZariskiSite} (h : W ≤ U)
    (B : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (z : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S n, B)) :
    (S.toGradedAffineAlgebra.twistπ n W).app B z =
      (S.toGradedAffineAlgebra.twistTransition n h).app B ((S.toGradedAffineAlgebra.twistπ n U).app B z) := by
  have e1 := ConcreteCategory.congr_hom (congrArg (fun k => AlgebraicGeometry.Scheme.Modules.Hom.app k B)
    (S.toGradedAffineAlgebra.twistπ_transition n h)) z
  refine e1.symm.trans ?_
  refine (congrArg (fun k => k z) (AlgebraicGeometry.Scheme.Modules.Hom.comp_app
    (S.toGradedAffineAlgebra.twistπ n U) (S.toGradedAffineAlgebra.twistTransition n h) (U := B))).trans ?_
  exact ConcreteCategory.comp_apply _ _ _

end AlgebraicGeometry.Scheme.relativeProj

end
