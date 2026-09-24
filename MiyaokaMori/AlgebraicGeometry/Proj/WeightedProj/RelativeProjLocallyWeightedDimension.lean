import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.RelativeDimensionAdd
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceDimension

/-! # Dimension of the relative Proj of a locally weighted polynomial algebra

Let `X` be a scheme locally of finite type over a field `k` and `S` a graded quasi-coherent algebra
on `X` which is locally the weighted polynomial algebra of weights `w` on a nonempty finite variable
set `σ`. Then `dim Proj_X S = dim X + (|σ| − 1)`.

Proof:
1. `relativeProj_locallyWeighted_localProduct`: there is an open cover of `X` over whose pieces
   `Proj_X S` is a product with `P_k(w)`, compatibly with the projections.
2. `P_k(w) → Spec k` is locally of finite type (`P_k(w) = Proj k[x_σ]` is covered by finitely many
   affine charts `Spec (k[x_σ]_{(x_i)})`, each a finitely generated `k`-algebra).
3. `dimension_eq_of_locally_product`: `dim Proj_X S = dim X + dim P_k(w)`.
4. `weightedProjectiveSpace_dimension`: `dim P_k(w) = |σ| − 1`.

This is the dimension count `dim Y_k^GG = dim C + (n+1)k − 1` in the Veronese polarization lemma of
the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- `dim Proj_X S = dim X + (|σ| − 1)` for a locally weighted polynomial algebra `S` on a scheme `X`
locally of finite type over a field. -/
theorem relativeProj_locallyWeighted_krullDim {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pX]
    (S : X.GradedQCAlgebra) {σ : Type u} [Fintype σ] [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) :
    topologicalKrullDim (AlgebraicGeometry.Scheme.relativeProj S).left =
      topologicalKrullDim X + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  have hft : AlgebraicGeometry.LocallyOfFiniteType
      (weightedProjectiveSpace k (σ := σ) w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.LocallyOfFiniteType
      (MiyaokaMori.WeightedJets.weightedProjToSpec k
        (fun i : σ => (⟨w i, hw i⟩ : ℕ+)))
    let A : ℕ → Submodule k (MvPolynomial σ k) :=
      MvPolynomial.weightedHomogeneousSubmodule k
        (fun i : σ => ((⟨w i, hw i⟩ : ℕ+) : ℕ))
    have hzero (p : A 0) :
        MvPolynomial.C (MvPolynomial.constantCoeff (p : MvPolynomial σ k)) =
          (p : MvPolynomial σ k) := by
      have hp : (p : MvPolynomial σ k).IsWeightedHomogeneous
          (fun i : σ => ((⟨w i, hw i⟩ : ℕ+) : ℕ)) 0 := p.2
      calc
        MvPolynomial.C (MvPolynomial.constantCoeff (p : MvPolynomial σ k)) =
            MvPolynomial.weightedHomogeneousComponent
              (fun i : σ => ((⟨w i, hw i⟩ : ℕ+) : ℕ)) 0
              (p : MvPolynomial σ k) := by
          simpa only [MvPolynomial.constantCoeff_eq] using
            (MvPolynomial.weightedHomogeneousComponent_zero (p : MvPolynomial σ k)
              (fun i : σ => Nat.ne_of_gt (hw i))).symm
        _ = (p : MvPolynomial σ k) := hp.weightedHomogeneousComponent_same
    let e : A 0 ≃+* k :=
      { toFun := fun p => MvPolynomial.constantCoeff (p : MvPolynomial σ k)
        invFun := fun r => ⟨MvPolynomial.C r,
          MvPolynomial.isWeightedHomogeneous_C
            (fun i : σ => ((⟨w i, hw i⟩ : ℕ+) : ℕ)) r⟩
        left_inv := fun p => Subtype.ext (hzero p)
        right_inv := fun r => MvPolynomial.constantCoeff_C σ r
        map_mul' := fun p q => map_mul MvPolynomial.constantCoeff _ _
        map_add' := fun p q => map_add MvPolynomial.constantCoeff _ _ }
    have hfinite : Algebra.FiniteType (A 0) (MvPolynomial σ k) := by
      have hst : IsScalarTower k (A 0) (MvPolynomial σ k) :=
        IsScalarTower.of_algebraMap_eq (R := k) (S := A 0)
          (A := MvPolynomial σ k) (fun _ ↦ rfl)
      exact Algebra.FiniteType.of_restrictScalars_finiteType k (A 0)
        (MvPolynomial σ k)
    have hproj : AlgebraicGeometry.LocallyOfFiniteType
        (AlgebraicGeometry.Proj.toSpecZero A) := by
      letI := hfinite
      infer_instance
    have he : e.symm.toRingHom = algebraMap k (A 0) := by
      apply RingHom.ext
      intro r
      apply Subtype.ext
      rfl
    have hiso : IsIso (CommRingCat.ofHom (algebraMap k (A 0))) := by
      rw [← he]
      exact e.symm.toCommRingCatIso.isIso_hom
    letI := hfinite
    letI := hiso
    change AlgebraicGeometry.LocallyOfFiniteType
      (AlgebraicGeometry.Proj.toSpecZero A ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (A 0))))
    have hspec : AlgebraicGeometry.LocallyOfFiniteType
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (A 0)))) := by
      rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.LocallyOfFiniteType)]
      exact RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (C := CommRingCat) (CommRingCat.ofHom (algebraMap k (A 0)))).surjective
    letI := hproj
    letI := hspec
    infer_instance
  obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct.{u, u} pX S w hw hS
  rw [← weightedProjectiveSpace_dimension k w hw]
  exact dimension_eq_of_locally_product pX
    (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (AlgebraicGeometry.Scheme.relativeProj S).hom 𝒰
    (fun i => by obtain ⟨φ, h1, _⟩ := h𝒰 i; exact ⟨φ, h1⟩)

end
