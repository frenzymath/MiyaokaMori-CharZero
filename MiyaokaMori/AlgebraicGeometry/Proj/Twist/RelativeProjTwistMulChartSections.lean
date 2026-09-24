import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulPointwise
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation

/-! # The 01NR comparison map on sections

The comparison map of Stacks 01NR, `twistAffineHom S U n : O(n)|_{π⁻¹U} ⟶ e_U^* O_U(n)`, followed by the
identification `e_U^* O_U(n) ≅ O_U(n)|_{e_U}` (`restrictFunctorIsoPullback`), is on sections over `A ⊆ π⁻¹U` the chart
projection `twistπ n U : O(n) ⟶ (c_U)_* O_U(n)` at `ι_U''A`, transported along `e_U''A = c_U⁻¹(ι_U''A)`
(`tAH_rFIP_inv_app`; pointwise version `tAH_rFIP_inv_app_val`). This is `chartSections_app`
(`TwistMultiplicationChartSections`) read through the definition of `twistAffineHom`.

Source: Stacks 01NR, 01LI. Used for the associativity of `twistMul` on sections (`RelativeProjTwistMulAssoc`).

**How the kernel is kept cheap**: the proof never unfolds `twistAffineHom`. It uses the
already proved section formula `twistAffineHom_app` (`TwistMultiplicationChartSections`; elaborator 0.3 s, kernel 4 s),
whose right-hand side is `twistπ.app (ι_U''A) ≫ presheafMapW (chartTwist S U n) (eqToHom _) ≫ rFIPhomApp e_U _ _ A`, and a
**variable-level** element lemma `rFIP_inv_app_apply_of_formula` (`(rFIP f)⁻¹ (F z) = s (t z)` given
`F.app A = t ≫ s ≫ rFIPhomApp f hf N A`). The element lemma is instantiated by `refine … ?_ z` **against the goal**, so all
its implicit data (`N = Proj.twist (S.sectionsGrading U.1) n`, `s = N.presheaf.map (eqToHom _).op`, `t = twistπ.app _`)
get the statement's spelling and the conclusion is syntactically the goal; the only remaining defeq check is
`twistAffineHom_app` against the hypothesis `?hF`, which differs from it only under **regular** heads
(`chartTwist S U n` vs `Proj.twist (S.sectionsGrading U.1) n`: one delta; `presheafMapW` vs `presheaf.map`: one delta;
`affineIso_image_eq_chartMap_preimage` vs `affineIso_image_eq_projChart_preimage`: proof irrelevance), where the kernel
compares arguments first. Whole file: 8 s single-file compile, no kernel hotspot above 0.5 s.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The nested form of the chart comparison shape (the literal body of `twistAffineHom`, followed by
`restrictFunctorIsoPullback⁻¹`, applied to a section) is `chartSectionsAux` applied to the section. Generic in all data,
`rfl` at the variable level. -/
theorem AlgebraicGeometry.Scheme.Modules.chartHomShape_app_app_eq_chartSectionsAux_app
    {Y P Z : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ P) (hιOI : AlgebraicGeometry.IsOpenImmersion ι)
    (e : Y ≅ Z) (heOI : AlgebraicGeometry.IsOpenImmersion e.hom) (c : Z ⟶ P) (hcOI : AlgebraicGeometry.IsOpenImmersion c)
    (p : ι = e.hom ≫ c) (T : P.Modules) (N : Z.Modules)
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback c).obj T ⟶ N) (A : Y.Opens)
    (z : Γ(@AlgebraicGeometry.Scheme.Modules.restrict _ _ T ι hιOI, A)) :
    ((@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _ _ e.hom heOI).inv.app N).app A
      (((@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _ _ ι hιOI).hom.app T ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr p).hom.app T ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom c).inv.app T ≫
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map φ).app A z) =
    (@AlgebraicGeometry.Scheme.Modules.chartSectionsAux _ _ _ ι hιOI e heOI c hcOI p T N φ).app A z := rfl

/-- Element form of `app_comp_rFIP_inv_eq_of_formulas` (`TwistMultiplicationChartSections`): if the section map of
`F : M ⟶ f^* N` factors as `F.app A = t ≫ s ≫ rFIPhomApp f hf N A` (the last factor being the component of
`restrictFunctorIsoPullback f` on sections), then `((rFIP f).inv.app N).app A (F.app A z) = s (t z)`.
Variable level only (schemes, morphisms, sheaves are variables), so the kernel check is immediate; concrete statements
are obtained by `refine … ?_ z` against the goal, so that the conclusion is syntactically the goal. -/
theorem AlgebraicGeometry.Scheme.Modules.rFIP_inv_app_apply_of_formula {Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ Z) (hf : AlgebraicGeometry.IsOpenImmersion f) (M : Y.Modules) (N : Z.Modules)
    (F : M ⟶ (AlgebraicGeometry.Scheme.Modules.pullback f).obj N) (A : Y.Opens)
    {W : AddCommGrpCat.{u}} (t : Γ(M, A) ⟶ W)
    (s : W ⟶ Γ((@AlgebraicGeometry.Scheme.Modules.restrictFunctor Y Z f hf).obj N, A))
    (hF : F.app A = t ≫ s ≫ AlgebraicGeometry.Scheme.Modules.rFIPhomApp f hf N A) (z : Γ(M, A)) :
    ((@AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Y Z f hf).inv.app N).app A (F.app A z) =
      s (t z) := by
  rw [hF]
  have h := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Scheme.Modules.rFIPhomApp_comp_inv_app f hf N A) (s (t z))
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h ⊢
  exact h

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- **The 01NR comparison map on sections**: for `A ⊆ π⁻¹U` and
`z ∈ Γ(O(n)|_{π⁻¹U}, A) = Γ(O(n), ι_U''A)`,

  `rFIP(e_U)⁻¹ (twistAffineHom S U n z) = (twistπ n U z)|_{e_U''A}`  in `Γ(O_U(n), e_U''A)`,

the restriction being along `e_U''A = c_U⁻¹(ι_U''A)` (`affineIso_image_eq_projChart_preimage`).

**Natural-language proof** (Stacks 01NR; complete). `twistAffineHom S U n` is by definition the composite
`rFIP(ι_U) ≫ pullbackCongr ≫ pullbackComp(e_U, c_U)⁻¹ ≫ e_U^*(twistChartHom n U)` (`Stacks01nr.lean`), and
`twistChartHom n U` is the adjoint transpose of the limit projection `twistπ n U` (`twistChartHom_eq`). Hence its
section map at `A` is `(twistπ n U).app (ι_U''A) ≫ res ≫ rFIP(e_U).app` (`twistAffineHom_app`,
`TwistMultiplicationChartSections`, proved: adjunction transposes of open-immersion restrictions), and composing with the
component of `rFIP(e_U)⁻¹` cancels the last factor (`rFIPhomApp_comp_inv_app`), which is exactly the claim.

**Formal proof**: `rFIP_inv_app_apply_of_formula` (variable level, above) instantiated against the goal, with the
hypothesis closed by `twistAffineHom_app S U n A` (see the module header for why this is cheap for the kernel: 8 s
single-file compile, whereas unfolding `twistAffineHom` inside the statement exceeded 60 s in the kernel). -/
theorem tAH_rFIP_inv_app (U : X.affineOpens) (n : ℤ) (A : ((relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens)
    (z : Γ((twist S n).restrict ((relativeProj S).hom ⁻¹ᵁ U.1).ι, A)) :
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (affineIso S U).hom).inv.app
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n)).app A ((twistAffineHom S U n).app A z) =
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n).presheaf.map
        (eqToHom (affineIso_image_eq_projChart_preimage S U A)).op
        ((S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)).app
          (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) z) := by
  refine AlgebraicGeometry.Scheme.Modules.rFIP_inv_app_apply_of_formula _ _ _ _ _ A _ _ ?_ z
  exact twistAffineHom_app S U n A

/-- Pointwise form of `tAH_rFIP_inv_app`: the value at `q ∈ e_U''A` of `χ_n z := rFIP(e_U)⁻¹ (twistAffineIso.hom z)` is
the value of `twistπ n U z` at the same point of `c_U⁻¹(ι_U''A)`. -/
theorem tAH_rFIP_inv_app_val (U : X.affineOpens) (n : ℤ) (A : ((relativeProj S).hom ⁻¹ᵁ U.1).toScheme.Opens)
    (z : Γ((twist S n).restrict ((relativeProj S).hom ⁻¹ᵁ U.1).ι, A))
    (q : ((affineIso S U).hom ''ᵁ A : (AlgebraicGeometry.Proj (S.sectionsGrading U.1)).Opens)) :
    Subtype.val (((twistAffineIso S U n).hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (affineIso S U).hom).inv.app
          (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n)).app A z :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.sectionsGrading U.1) n
          ((affineIso S U).hom ''ᵁ A)) q =
      Subtype.val ((S.toGradedAffineAlgebra.twistπ n (AlgebraicGeometry.Scheme.affineSite U)).app
          (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A) z :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
          (S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U)) n
          (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite U) ⁻¹ᵁ
            (((relativeProj S).hom ⁻¹ᵁ U.1).ι ''ᵁ A)))
        ⟨q.1, leOfHom (eqToHom (affineIso_image_eq_projChart_preimage S U A)) q.2⟩ := by
  rw [twistAffineIso_hom]
  have h := congrArg (fun s => Subtype.val (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule
    (S.sectionsGrading U.1) n ((affineIso S U).hom ''ᵁ A)) q) (tAH_rFIP_inv_app S U n A z)
  exact h.trans (AlgebraicGeometry.Proj.twist_presheaf_map_val (S.sectionsGrading U.1) n _ _ q)

end AlgebraicGeometry.Scheme.relativeProj

end
