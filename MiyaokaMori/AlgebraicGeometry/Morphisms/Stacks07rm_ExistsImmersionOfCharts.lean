import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.EpiOfTransposeFrames
import MiyaokaMori.AlgebraicGeometry.Modules.FrameLocusOn
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Morphisms.ImmersionIntoProjSymOfCharts
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Existence of the immersion `X → P(E)` from chart data

**Existence form of the immersion criterion for `X → P(E)`** (Stacks 07RM, fifth paragraph): under the chart
hypotheses of `relativeProj.isImmersion_lift_symGradedAlgebra_of_charts` there is an immersion
`r : X ⟶ Proj_S (Sym E)` over `S`.

**Proof.** Take `r := relativeProj.lift (Sym E) f M (liftDataOfEpi f E M ψ hψ)` (`RelativeProjLift.lean`,
`RelativeProjLiftDataOfEpi.lean`); `r ≫ π = f` is `relativeProj.lift_hom` and `IsImmersion r` is
`relativeProj.isImmersion_lift_symGradedAlgebra_of_charts` (`Stacks07rm_LiftSymImmersionOfCharts.lean`, where the
mathematics of 07RM paragraph 5 lives) applied to the same data. `transposeSection` below and `transposeSection`
there are definitionally equal abbreviations, so `hcharts` is accepted verbatim. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Existence of the immersion `X → P(E)` from chart data** (Stacks 07RM paragraph 5): if every point has an
affine chart `(V, e)` on which `s = φ(e)` has affine frame locus `X_s` with `Γ(X_s, O)` generated over `Γ(V, O)`
by the ratios `φ(e')/s`, then there is an immersion `r : X ⟶ Proj_S (Sym E)` with `r ≫ π = f`
(namely `relativeProj.lift` of `liftDataOfEpi f E M ψ hψ`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.exists_isImmersion_symGradedAlgebra_of_charts
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (M : X.Modules) [M.IsLineBundle]
    (E : S.Modules) [E.IsQuasicoherent] (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj E ⟶ M)
    (hψ : CategoryTheory.Epi ψ)
    (hcharts : ∀ x : X, ∃ (V : S.affineOpens) (e : Γ(E, V.1)),
      x ∈ M.frameLocusOn (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e) ∧
      AlgebraicGeometry.IsAffineOpen (M.frameLocusOn (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e)) ∧
      Subring.closure
        (Set.range (f.appLE V.1 (M.frameLocusOn (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e))
          (M.frameLocusOn_le (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e))) ∪
        {g | ∃ e' : Γ(E, V.1),
          M.res (M.frameLocusOn_le (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e))
              (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e') =
            g • M.res (M.frameLocusOn_le (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e))
              (AlgebraicGeometry.Scheme.Modules.transposeSection f ψ e)}) = ⊤) :
    ∃ r : X ⟶ (AlgebraicGeometry.Scheme.relativeProj (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra E)).left,
      AlgebraicGeometry.IsImmersion r ∧
      r ≫ (AlgebraicGeometry.Scheme.relativeProj (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra E)).hom = f :=
  ⟨AlgebraicGeometry.Scheme.relativeProj.lift (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra E) f M
      (AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi f E M ψ hψ),
    AlgebraicGeometry.Scheme.relativeProj.isImmersion_lift_symGradedAlgebra_of_charts f M E ψ hψ hcharts,
    AlgebraicGeometry.Scheme.relativeProj.lift_hom _ _ _ _⟩

end
