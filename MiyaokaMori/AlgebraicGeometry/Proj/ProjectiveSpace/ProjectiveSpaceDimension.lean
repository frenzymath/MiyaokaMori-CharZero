import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionOpenCoverSup
import MiyaokaMori.RingTheory.WeightedAwayDegreeOneVariable
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceChartPolynomial
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! # The dimension of projective space

Ordinary projective space `P^N_k` (the weighted projective space with `N + 1` coordinates, all of
weight `1`) has dimension `N`. This is the case `k = 1` of the fibre dimension `(n+1)k − 1` of the
weighted projective spaces of §2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

theorem weightedProjectiveSpace_one_dimension (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    [Nonempty σ] :
    topologicalKrullDim (weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos)) =
      ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  have hcardpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr inferInstance
  have hcard : Fintype.card σ - 1 + 1 = Fintype.card σ := by omega
  let τ := Fin (Fintype.card σ - 1 + 1)
  let eσ : σ ≃ τ := (Fintype.equivFin σ).trans (finCongr hcard.symm)
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => (1 : ℕ))
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : τ => (1 : ℕ))
  let 𝒜σ := MiyaokaMori.WeightedJets.weightedPolynomialGrading k
    (fun _ : σ => (1 : ℕ+))
  let 𝒜Fin := MvPolynomial.homogeneousSubmodule τ k
  have hgrFin : GradedRing (MvPolynomial.homogeneousSubmodule τ k) :=
    MvPolynomial.gradedAlgebra
  letI : GradedRing (MvPolynomial.homogeneousSubmodule τ k) := hgrFin
  let eRing : MvPolynomial σ k ≃+* MvPolynomial τ k :=
    (MvPolynomial.renameEquiv k eσ).toRingEquiv
  have he : ∀ i (a : MvPolynomial σ k), a ∈ 𝒜σ i ↔ eRing a ∈ 𝒜Fin i := by
    intro i a
    change a ∈ MvPolynomial.weightedHomogeneousSubmodule k
        (fun _ : σ => (1 : ℕ)) i ↔
      eRing a ∈ MvPolynomial.homogeneousSubmodule τ k i
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule,
      MvPolynomial.mem_homogeneousSubmodule]
    have hweights : (fun _ : σ => (1 : ℕ)) = (1 : σ → ℕ) := by ext; simp
    constructor
    · intro ha
      have ha' : a.IsHomogeneous i := by
        simpa only [MvPolynomial.IsHomogeneous, hweights] using ha
      exact ha'.rename_isHomogeneous
    · intro ha
      have ha' : a.IsHomogeneous i := by
        rw [← MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff eσ.injective]
        simpa [eRing] using ha
      simpa only [MvPolynomial.IsHomogeneous, hweights] using ha'
  let iso : AlgebraicGeometry.Proj 𝒜σ ≅ AlgebraicGeometry.Proj 𝒜Fin :=
    AlgebraicGeometry.Proj.isoOfRingEquiv eRing he
  have hdimFin : topologicalKrullDim (AlgebraicGeometry.Proj 𝒜Fin) =
      ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
    let 𝒰 : (AlgebraicGeometry.Proj 𝒜Fin).OpenCover :=
      AlgebraicGeometry.Scheme.Cover.mkOfCovers
        τ
        (fun i : τ =>
          (AlgebraicGeometry.Proj.basicOpen 𝒜Fin (MvPolynomial.X i)).toScheme)
        (fun i : τ =>
          (AlgebraicGeometry.Proj.basicOpen 𝒜Fin (MvPolynomial.X i)).ι)
        (by
          intro x
          have htop : (⨆ i : τ,
              AlgebraicGeometry.Proj.basicOpen 𝒜Fin (MvPolynomial.X i)) = ⊤ := by
            apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
            · exact fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩
            · apply top_unique
              intro p hp
              clear hp
              induction p using MvPolynomial.induction_on with
              | C r =>
                exact (Algebra.adjoin (𝒜Fin 0)
                    (Set.range (MvPolynomial.X : τ → MvPolynomial τ k))).algebraMap_mem
                  ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C τ r⟩
              | add p q hp hq => exact Subalgebra.add_mem _ hp hq
              | mul_X p i hp =>
                exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self i))
          have hx : x ∈ (⨆ i : τ,
              AlgebraicGeometry.Proj.basicOpen 𝒜Fin (MvPolynomial.X i)) := by
            rw [htop]
            trivial
          obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
          exact ⟨i, ⟨x, hi⟩, rfl⟩)
    rw [topologicalKrullDim_eq_iSup_openCover 𝒰]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      change τ at i
      let e := @AlgebraicGeometry.Proj.basicOpenIsoSpec
        (Submodule k (MvPolynomial τ k)) (MvPolynomial τ k) _ _ _
        𝒜Fin hgrFin (MvPolynomial.X i)
        (m := 1)
        ((MvPolynomial.mem_homogeneousSubmodule (σ := τ) (R := k) 1
          (MvPolynomial.X i)).mpr (MvPolynomial.isHomogeneous_X k i)) (by simp)
      rw [show 𝒰.X i =
          (AlgebraicGeometry.Proj.basicOpen 𝒜Fin (MvPolynomial.X i)).toScheme from rfl]
      rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
      change topologicalKrullDim (AlgebraicGeometry.Spec _) ≤ _
      erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      rw [ringKrullDim_eq_of_ringEquiv (ProjectiveSpace.chartRingEquiv
        (Fintype.card σ - 1) k i)]
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
      simp
    · let i₀ : τ := ⟨0, by omega⟩
      have hdim₀ : topologicalKrullDim (𝒰.X i₀) =
          ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
        let e := @AlgebraicGeometry.Proj.basicOpenIsoSpec
          (Submodule k (MvPolynomial τ k)) (MvPolynomial τ k) _ _ _
          𝒜Fin hgrFin (MvPolynomial.X i₀) (m := 1)
          ((MvPolynomial.mem_homogeneousSubmodule (σ := τ) (R := k) 1
            (MvPolynomial.X i₀)).mpr (MvPolynomial.isHomogeneous_X k i₀)) (by simp)
        rw [show 𝒰.X i₀ =
            (AlgebraicGeometry.Proj.basicOpen 𝒜Fin (MvPolynomial.X i₀)).toScheme from rfl]
        rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
        change topologicalKrullDim (AlgebraicGeometry.Spec _) = _
        erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
        rw [ringKrullDim_eq_of_ringEquiv (ProjectiveSpace.chartRingEquiv
          (Fintype.card σ - 1) k i₀)]
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
        simp
      exact le_iSup_of_le i₀ (by rw [hdim₀])
  change topologicalKrullDim (MiyaokaMori.WeightedJets.weightedProj k
    (fun _ : σ => (1 : ℕ+))) = _
  change topologicalKrullDim (AlgebraicGeometry.Proj 𝒜σ) = _
  rw [iso.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq, hdimFin]

end
