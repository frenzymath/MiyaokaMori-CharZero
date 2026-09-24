import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjGradedDomainIrreducible
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceNormal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Stacks020j

/-! # Integrality of products with weighted projective space

Weighted projective space is integral (the "irreducible and normal" part of Dolgachev, *Weighted
projective varieties*, Proposition 1.3.3(i)), extended to the local products used in the paper: if
`U` is integral and normal over `k`, then `U ×_k P(w)` is integral (proof of the Veronese polarization
lemma). Normality of `U` is supplied at the call sites by "smooth of dimension `≤ 1`".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `U ×_k P(w)` is integral for an integral normal irreducible `k`-scheme `U`. -/
theorem weightedProjectiveSpace_prod_isIntegral (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {σ : Type u} [Fintype σ] [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : AlgebraicGeometry.Scheme.{u}) (pU : U ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsIntegral U] [U.IsNormal] [IrreducibleSpace U] :
    AlgebraicGeometry.IsIntegral (CategoryTheory.Limits.pullback pU
      (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
  let P : AlgebraicGeometry.Scheme.{u} := weightedProjectiveSpace k w hw
  let pP : P ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let Xprod : AlgebraicGeometry.Scheme.{u} := CategoryTheory.Limits.pullback pU pP
  have hPirr : IrreducibleSpace P := by
    letI : GradedRing (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
        (fun i : σ => (⟨w i, hw i⟩ : ℕ+))) :=
      MvPolynomial.weightedGradedAlgebra (R := k) (w := fun i : σ => w i)
    change IrreducibleSpace (AlgebraicGeometry.Proj
      (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
        (fun i : σ => (⟨w i, hw i⟩ : ℕ+))))
    apply AlgebraicGeometry.Proj.irreducibleSpace_of_isDomain
    let i : σ := Classical.choice (inferInstance : Nonempty σ)
    refine ⟨w i, MvPolynomial.X i, ?_, ?_, ?_⟩
    · exact hw i
    · exact (MvPolynomial.mem_weightedHomogeneousSubmodule k _ _ _).mpr
        (MvPolynomial.isWeightedHomogeneous_X k (fun j => (w j : ℕ)) i)
    · exact MvPolynomial.X_ne_zero i
  letI : IrreducibleSpace P := hPirr
  letI : AlgebraicGeometry.GeometricallyIrreducible pP := by
    rw [AlgebraicGeometry.GeometricallyIrreducible.eq_geometrically]
    rw [AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    exact AlgebraicGeometry.irreducibleSpace_pullback_of_isSepClosed P pP
  letI : AlgebraicGeometry.UniversallyOpen pP := by
    exact inferInstance
  letI : IrreducibleSpace Xprod := by
    exact inferInstance
  have hN : Xprod.IsNormal :=
    weightedProjectiveSpace_prod_isNormal k w hw U pU
  letI : Xprod.IsNormal := hN
  letI : ∀ x : Xprod,
      _root_.IsReduced (Xprod.presheaf.stalk x) := by
    intro x
    letI : IsDomain (Xprod.presheaf.stalk x) :=
      hN.isDomain x
    infer_instance
  letI : AlgebraicGeometry.IsReduced Xprod :=
    AlgebraicGeometry.isReduced_of_isReduced_stalk Xprod
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

end
