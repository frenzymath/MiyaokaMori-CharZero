import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjGradedDomainIrreducible
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra

/-! # Weighted projective space is integral

For positive weights and a nonempty set of coordinates, `P_k(w) = Proj k[x_σ]` is an integral
scheme. The general form is `AlgebraicGeometry.Proj.isIntegral_of_isDomain`: the `Proj` of a graded
domain with a nonzero homogeneous element of positive degree is integral.

References: Stacks 01MB (the standard open cover of `Proj`), EGA II 2.4.7. Integrality of `P(w)` is
an instance hypothesis of the degree computation for the power map.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Integrality of `Proj`**: if `A` is a domain with grading `𝒜` and there is a nonzero homogeneous
element of positive degree (so that `Proj` is nonempty), then `Proj 𝒜` is an integral scheme.
Irreducibility: `Proj.irreducibleSpace_of_isDomain`; reducedness: every stalk is
`≅ HomogeneousLocalization.AtPrime 𝒜 p` (`Proj.stalkIso`), which embeds via `val` into the domain
`Localization.AtPrime p`, hence is a domain, and `isReduced_of_isReduced_stalk`. -/
theorem AlgebraicGeometry.Proj.isIntegral_of_isDomain {A σ : Type u} [CommRing A] [IsDomain A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (h : ∃ (m : ℕ) (f : A), 0 < m ∧ f ∈ 𝒜 m ∧ f ≠ 0) :
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Proj 𝒜) := by
  have hirr : IrreducibleSpace (AlgebraicGeometry.Proj 𝒜) :=
    AlgebraicGeometry.Proj.irreducibleSpace_of_isDomain 𝒜 h
  have hstalk : ∀ x : AlgebraicGeometry.Proj 𝒜,
      _root_.IsReduced ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) := by
    intro x
    have hp : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    let φ : HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal →+*
        Localization.AtPrime x.asHomogeneousIdeal.toIdeal :=
      { toFun := HomogeneousLocalization.val
        map_one' := HomogeneousLocalization.val_one
        map_mul' := HomogeneousLocalization.val_mul
        map_zero' := HomogeneousLocalization.val_zero
        map_add' := HomogeneousLocalization.val_add }
    have hdomA : IsDomain (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
      Function.Injective.isDomain φ (HomogeneousLocalization.val_injective _)
    have hdomA' : IsDomain
        (CommRingCat.of (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) : Type u) :=
      hdomA
    let e := (AlgebraicGeometry.Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv
    have hdom : IsDomain ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) :=
      Function.Injective.isDomain e.toRingHom e.injective
    infer_instance
  have hred : AlgebraicGeometry.IsReduced (AlgebraicGeometry.Proj 𝒜) :=
    @AlgebraicGeometry.isReduced_of_isReduced_stalk _ hstalk
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- `P_k(w) = Proj k[x_i : i ∈ σ]` (`deg x_i = w_i > 0`, `σ` nonempty) is an integral scheme: by
`Proj.isIntegral_of_isDomain`, `k[x_σ]` is a domain and `x_i` (any `i ∈ σ`) is a nonzero homogeneous
element of degree `w_i > 0`. Edge case: for `σ = ∅`, `Proj k = ∅` is not integral, hence `[Nonempty σ]`. -/
theorem weightedProjectiveSpace.isIntegral (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    AlgebraicGeometry.IsIntegral (weightedProjectiveSpace k w hw) := by
  let _ : GradedRing (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
      (fun i : σ => (⟨w i, hw i⟩ : ℕ+))) :=
    MvPolynomial.weightedGradedAlgebra (R := k) (w := fun i : σ => w i)
  change AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Proj
    (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun i : σ => (⟨w i, hw i⟩ : ℕ+))))
  apply AlgebraicGeometry.Proj.isIntegral_of_isDomain
  let i : σ := Classical.choice (inferInstance : Nonempty σ)
  refine ⟨w i, MvPolynomial.X i, hw i, ?_, MvPolynomial.X_ne_zero i⟩
  exact (MvPolynomial.mem_weightedHomogeneousSubmodule k _ _ _).mpr
    (MvPolynomial.isWeightedHomogeneous_X k (fun j => (w j : ℕ)) i)

end
