import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationOfBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The split weighted coordinates

The `i`-th coordinate `x_{i,q}` of weight `q`: a global section of `O_{Y^sp}(q) ⊗ π_sp^*Q_i` on `Y^sp`, given by
the copy of `Q_i^∨` in the weight-`q` graded piece and the tautological pairing (`Q_i = F.lineQuotient i`);
see the proof of Proposition 2.4 of the paper ("the weight-`q` coordinate takes values in `Q_i`").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `x_{i,q} ∈ Γ(Y^sp, O(q) ⊗ π^*Q_i)` (`Q_i = F.lineQuotient i`, `1 ≤ q ≤ kk`). Construction:
`ι_{i,q} : Q_i^∨ → (⊕_j Q_j)^∨ → S^sp_q` is the dual of the `i`-th projection followed by the inclusion of the
weight-`q` generators (the `(q-1)`-st copy of the generator sheaf `(⊕_j Q_j)^∨` of `S^sp = splitWeightedAlgebraOf F kk`
has weight `q`); `φ : π^*Q_i^∨ → π^*S_q → O(q)` is the pullback followed by the canonical evaluation of the
relative Proj; `x_{i,q} := (φ ⊗ id)(π^* coev_{Q_i})`, where the coevaluation section `coev ∈ Γ(C, Q_i^∨ ⊗ Q_i)`
is pulled back along `π` (`sectionPullbackAlong`), moved through `π^*(Q^∨ ⊗ Q) → π^*Q^∨ ⊗ π^*Q`
(`pullbackTensorObjHom`, the forward direction of `pullbackTensorIso`) and then `φ ⊗ id` is applied
(`Modules.tensor` and the monoidal `⊗` are interchanged via `tensorIsoTensorObj`).
Locally, for a frame `ε` of `Q_i`, `coev = ε^∨ ⊗ ε` and `x_{i,q} = (copy of ε^∨) ⊗ ε`: the weight-`q` coordinate
takes values in `Q_i`, as in the paper. -/

noncomputable def splitWeightedCoord {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n kk : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1))
    (i : Fin (n + 1)) (q : ℕ) (hq : q ∈ Finset.Icc 1 kk) :
    ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (q : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (splitWeightedProjectivization F kk).hom).obj
            (F.lineQuotient i).toModules)).val.obj (Opposite.op ⊤) :=
  haveI : ∀ j : Fin (n + 1), (F.lineQuotient j).toModules.IsLocallyFree := fun j => (F.lineQuotient j).locallyFree
  haveI : ∀ j : Fin (n + 1), (F.lineQuotient j).toModules.IsFiniteType := fun j => (F.lineQuotient j).isFiniteType
  let S := splitWeightedAlgebraOf F kk
  let π := (splitWeightedProjectivization F kk).hom
  let Q := (F.lineQuotient i).toModules
  let V : Fin kk → C.toScheme.Modules := fun _ =>
    CategoryTheory.Limits.biproduct (fun j : Fin (n + 1) => (F.lineQuotient j).toModules)
  have hq' : 1 ≤ q ∧ q ≤ kk := Finset.mem_Icc.mp hq
  let j₀ : Fin kk := ⟨q - 1, by omega⟩
  -- ι_{i,q} : Q_i^∨ → S_q
  let ι : AlgebraicGeometry.Scheme.Modules.dual Q ⟶ S.part q :=
    AlgebraicGeometry.Scheme.Modules.dualMap
        (CategoryTheory.Limits.biproduct.π (fun j : Fin (n + 1) => (F.lineQuotient j).toModules) i) ≫
      AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl V j₀ ≫
      CategoryTheory.eqToHom (congrArg S.part (by simp only [j₀]; omega))
  -- φ : π^*Q_i^∨ → O(q)
  let φ : (AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.dual Q) ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ) :=
    (AlgebraicGeometry.Scheme.Modules.pullback π).map ι ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S q
  -- φ ⊗ id : π^*Q^∨ ⊗ π^*Q → O(q) ⊗ π^*Q
  let Φ : AlgebraicGeometry.Scheme.Modules.tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.dual Q))
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q) ⟶
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q) :=
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
      CategoryTheory.MonoidalCategoryStruct.whiskerRight φ _ ≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv
  -- `π^* coev_Q`, moved through `π^*(Q^∨ ⊗ Q) → π^*Q^∨ ⊗ π^*Q`
  let c : ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual Q) Q)).val.obj (Opposite.op ⊤) :=
    sectionPullbackAlong π (AlgebraicGeometry.Scheme.Modules.coevSection Q)
  Φ.app ⊤ ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π (AlgebraicGeometry.Scheme.Modules.dual Q) Q).hom.app ⊤ c)

end
