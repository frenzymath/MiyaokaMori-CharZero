import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQCAlgebraSpecPolynomialIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # The pullback of a locally weighted polynomial algebra to a residue field

For a locally weighted polynomial graded quasi-coherent algebra `S` (atlas form), the pullback
`GradedQCAlgebra.pullback` along `Spec κ(x) → X` is isomorphic to the standard weighted polynomial
algebra `weightedPolynomialQCAlgebra (Spec κ(x)) w hw` over the residue field.

Proof:
1. `IsLocallyWeightedPolynomial` is preserved under pullback along any morphism
   (`IsLocallyWeightedPolynomial.pullback`, whose core `weightedPolynomialAtlas_pullback` is Stacks
   01I9), so `T := S.pullback (Spec κ(x) → X)` has a weighted polynomial atlas.
2. `Spec κ(x)` has a single point (the `Unique` instance of `PrimeSpectrum`), and the chart containing
   it is `⊤`.
3. The chart data on `⊤` is `T.sectionsRing ⊤ ≃+* MvPolynomial σ Γ(Spec κ(x), ⊤)` (graded pieces ↔
   weighted homogeneous components, structure map ↔ `C`); since every graded piece is a free sheaf
   (quasi-coherent with a basis of global sections) and multiplication and unit are compatible on
   generators, `T ≅ weightedPolynomialQCAlgebra (Spec κ(x)) w hw`.

References: Stacks 01I7, 01I9.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `S` pulled back to `Spec κ(x)` is the weighted polynomial algebra over `κ(x)`. -/
theorem weightedProjectivizationFiber_local_alg_iso
    {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) (x : X) :
    ∃ _q : S.pullback (X.fromSpecResidueField x) ≅
      AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
        (AlgebraicGeometry.Spec (CommRingCat.of (X.residueField x))) w hw, True := by
  have hT := AlgebraicGeometry.Scheme.GradedQCAlgebra.IsLocallyWeightedPolynomial.pullback
    (X.fromSpecResidueField x) S w hw hS
  obtain ⟨𝒜⟩ := ((S.pullback (X.fromSpecResidueField x)).isLocallyWeightedPolynomial_iff w hw).mp hT
  let y₀ : AlgebraicGeometry.Spec (CommRingCat.of (X.residueField x)) :=
    (default : PrimeSpectrum (X.residueField x))
  obtain ⟨i, hi⟩ := 𝒜.covers y₀
  have hV : (𝒜.chart i).toOpens = ⊤ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_top]
    refine Set.eq_univ_of_forall (fun y => ?_)
    have hy : y = y₀ := Subsingleton.elim (α := PrimeSpectrum (X.residueField x)) y y₀
    rw [hy]
    exact hi
  obtain ⟨q⟩ := AlgebraicGeometry.Scheme.GradedQCAlgebra.exists_iso_weightedPolynomialQCAlgebra_of_sectionsRing_equiv
    (S.pullback (X.fromSpecResidueField x)) w hw (𝒜.chart i).toOpens hV (𝒜.equiv i)
    (𝒜.equiv_grading i) (𝒜.equiv_unit i)
  exact ⟨q, trivial⟩


end
