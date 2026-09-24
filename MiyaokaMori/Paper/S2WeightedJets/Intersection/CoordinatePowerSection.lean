import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitCoordBasicOpen
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedCoordinate
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinatePowerTwistLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinatePowerNonzeroLocus
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationOfBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The coordinate power sections

The `m/q`-th power (`q ∣ m`) of the weight-`q` coordinate `x_{i,q}` gives a global section `σ_{i,q}` of
`L_{i,q} := O_{Y^sp}(m) ⊗ π_sp^*Q_i^{⊗ m/q}` whose nonvanishing locus is exactly the relative basic open set
`D_+(x_{i,q})`. The construction uses the multiplication map of the twisting sheaves
`(O(q) ⊗ π^*Q_i)^{⊗(m/q)} → O(m) ⊗ π^*Q_i^{⊗(m/q)}` (in general not an isomorphism on a weighted Proj); see the proof
of Proposition 2.4 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- σ_p = x_{i,q}^{m/q}, p = (i, q-1) -/

noncomputable def coordPowSection {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n kk : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (m : ℕ)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) (p : Fin (n + 1) × Fin kk) :
    ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1))))).val.obj (Opposite.op ⊤) :=
  -- the multiplication of twisting sheaves `(O(q) ⊗ π^*Q_i)^{⊗(m/q)} ⟶ O(m) ⊗ π^*Q_i^{⊗(m/q)}` (`q ∣ m`)
  splitTwistMul F kk p.1 ((p.2 : ℕ) + 1) m (hdiv _ (by simp only [Finset.mem_Icc]; omega))
    (AlgebraicGeometry.Scheme.Modules.tensorPowSection
      (splitWeightedCoord F p.1 ((p.2 : ℕ) + 1) (by simp only [Finset.mem_Icc]; omega)) (m / ((p.2 : ℕ) + 1)))

/-- The sheaf `O(m) ⊗ π^*Q_i^{⊗(m/q)}` containing `σ_p` is a line bundle: when `m` is divisible by all weights
`1, …, kk`, `O(m)` is invertible, and pullbacks, tensor powers and tensor products of line bundles are line bundles. -/

private theorem splitWeightedTwist_isLineBundle_of_dvd {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) :
    (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).IsLineBundle := by
  exact splitWeightedTwist_isLineBundle_of_dvd_lemma F m hm hdiv

theorem coordPowSection_isLineBundle {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n kk : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (m : ℕ)
    (hm : 0 < m) (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) (p : Fin (n + 1) × Fin kk) :
    ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient p.1).toModules
            (m / ((p.2 : ℕ) + 1))))).IsLineBundle := by
  letI : (AlgebraicGeometry.Scheme.relativeProj.twist
      (splitWeightedAlgebraOf F kk) (m : ℤ)).IsLineBundle :=
    splitWeightedTwist_isLineBundle_of_dvd F m hm hdiv
  letI : (AlgebraicGeometry.Scheme.Modules.tensorPow
      (F.lineQuotient p.1).toModules (m / ((p.2 : ℕ) + 1))).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensorPow _ _
  letI : ((AlgebraicGeometry.Scheme.Modules.pullback
      (splitWeightedProjectivization F kk).hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          (F.lineQuotient p.1).toModules (m / ((p.2 : ℕ) + 1)))).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback
      (splitWeightedProjectivization F kk).hom _
  exact SheafOfModules.IsLineBundle.tensor _ _

/-- The nonvanishing locus of `σ_p` is exactly the relative basic open set `D_+(x_{i,q})` (on an affine open `V ⊆ C`
trivializing `Q_i`, `π⁻¹(V) = Proj_{O(V)} O(V)[x]` and this open set is `Proj.basicOpen x_{i,q}`). -/

private theorem coordPowSection_nonzeroLocus_bridge {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) (p : Fin (n + 1) × Fin kk) :
    haveI := coordPowSection_isLineBundle F m hm hdiv p
    (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection _ (coordPowSection F m hdiv p)).support)ᶜ
      = ((splitCoordBasicOpen F kk p : (splitWeightedProjectivization F kk).left.Opens) :
      Set (splitWeightedProjectivization F kk).left) := by
  letI := coordPowSection_isLineBundle F m hm hdiv p
  exact coordPowSection_nonzeroLocus_formula F m hm hdiv p
    (coordPowSection F m hdiv p) (by rfl) inferInstance

theorem coordPowSection_nonzeroLocus {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n kk : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (m : ℕ)
    (hm : 0 < m) (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) (p : Fin (n + 1) × Fin kk) :
    haveI := coordPowSection_isLineBundle F m hm hdiv p
    (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection _ (coordPowSection F m hdiv p)).support)ᶜ
      = ((splitCoordBasicOpen F kk p : (splitWeightedProjectivization F kk).left.Opens) :
          Set (splitWeightedProjectivization F kk).left) := by
  exact coordPowSection_nonzeroLocus_bridge F m hm hdiv p

end
