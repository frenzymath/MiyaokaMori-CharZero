import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.HyperplaneGradedHom
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLocalIso

/-! # The hyperplane of projective space, part 3: `θ : j^* O_{P^{m+1}}(1) ⟶ O_{P^m}(1)` is an isomorphism

Step 6 of the docstring of `projectiveSpace_hyperplane_iso` (Stacks 01MX for the graded surjection
`φ : K[x_0..x_{m+1}] → K[y_0..y_m]`, `x_{m+1} ↦ 0`). Proof by the stalk criterion
(`moduleHom_isIso_iff_stalk_bijective`): at `y ∈ D_+(y_j) = j⁻¹ D_+(x_j)`, the composite of the (bijective)
pullback-stalk tensor map `O_y ⊗_{O_x} O(1)_x → (j^*O(1))_y` with `θ_y` sends `b ⊗ germ x_j` to
`b • germ (ψ x_j) = b • germ y_j` (`moduleStalkMap_transpose_unit_germ`,
`twistToPushforward_app_homogeneousSection`); since `x_j` is a frame of `O(1)` on `D_+(x_j)` every element of the
tensor product is a pure tensor `b ⊗ germ x_j` (`IsFrame.stalkEquiv`), and `y_j` is a frame on `D_+(y_j)`, so the
composite is bijective. Source: Stacks 01MX; used for `Y₁^GG = P(E)` in Proposition 2.4
of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry HomogeneousIdeal TensorProduct

noncomputable section

namespace ProjBundleFiberDegreeOne

open AlgebraicGeometry MiyaokaMori.WeightedJets.ProjTwisting AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra

/-- The comparison map `ψ : O_{Proj 𝒜}(d) ⟶ (Proj.map f)_* O_{Proj ℬ}(d)` sends the canonical section `a/1`
(`a ∈ 𝒜 d`) to `f(a)/1`. -/
theorem twistToPushforward_app_homogeneousSection {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (d : ℕ) (a : A) (ha : a ∈ 𝒜 d) (W : (Proj 𝒜).Opens) :
    (Proj.twistToPushforward f hf (d : ℤ)).app W (homogeneousSection 𝒜 d a ha W) =
      homogeneousSection ℬ d (f a) (f.map_mem ha) (Proj.map f hf ⁻¹ᵁ W) := by
  apply Subtype.ext
  funext y
  have := y.1.isPrime
  have := (ProjectiveSpectrum.comap f hf y.1).isPrime
  change Localization.localRingHom _ _ (f : A →+* B) rfl (Localization.mk a 1) = Localization.mk (f a) 1
  rw [Localization.localRingHom_mk]
  congr 1
  exact Subtype.ext (map_one _)

variable (K : Type u) [Field K] (m : ℕ)

/-- **Stacks 01MX for the hyperplane surjection**: `θ : j^* O_{P^{m+1}}(1) ⟶ O_{P^m}(1)` is an isomorphism. -/
theorem isIso_twistPullbackHom_hyperplane :
    IsIso (Proj.twistPullbackHom (hyperplaneGradedHom K m) (irrelevant_le_map_hyperplaneGradedHom K m) 1) := by
  set ρ := Proj.map (hyperplaneGradedHom K m) (irrelevant_le_map_hyperplaneGradedHom K m) with hρdef
  rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
  intro y
  obtain ⟨j, hyj⟩ : ∃ j : Fin (m + 1), y ∈ Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K m) (X j) := by
    have hy : y ∈ (⊤ : (Proj (AlgebraicGeometry.Proj.projectiveGrading K m)).Opens) := trivial
    rw [← projectiveSpace_iSup_basicOpen_X K m] at hy
    exact Opens.mem_iSup.mp hy
  set U : (Proj (AlgebraicGeometry.Proj.projectiveGrading K (m + 1))).Opens :=
    Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X j.castSucc) with hUdef
  have hyV : y ∈ ρ ⁻¹ᵁ U := by
    change y ∈ Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K m) (hyperplaneGradedHom K m (X j.castSucc))
    rw [hyperplaneGradedHom_X_castSucc]
    exact hyj
  have hxU : ρ.base y ∈ U := hyV
  set eA := homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1 (X j.castSucc) (X_mem_one K m _) U
    with heA
  have hfA : IsFrame (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1) U eA :=
    isFrame_homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1 (X j.castSucc) (X_mem_one K m _) U
      fun z => z.2
  set eB := homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading K m) 1 (hyperplaneGradedHom K m (X j.castSucc))
    ((hyperplaneGradedHom K m).map_mem (X_mem_one K m _)) (ρ ⁻¹ᵁ U) with heB
  have hfB : IsFrame (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K m) 1) (ρ ⁻¹ᵁ U) eB :=
    isFrame_homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading K m) 1 (hyperplaneGradedHom K m (X j.castSucc))
      ((hyperplaneGradedHom K m).map_mem (X_mem_one K m _)) (ρ ⁻¹ᵁ U) fun z => z.2
  have hT := MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective ρ
    (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1) y
  rw [← Function.Bijective.of_comp_iff _ hT]
  set gA := (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1).presheaf.germ U (ρ.base y) hxU eA with hgA
  set gB := (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K m) 1).presheaf.germ (ρ ⁻¹ᵁ U) y hyV eB with hgB
  have key : ∀ b : (Proj (AlgebraicGeometry.Proj.projectiveGrading K m)).presheaf.stalk y,
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap _ y (Proj.twistPullbackHom (hyperplaneGradedHom K m) (irrelevant_le_map_hyperplaneGradedHom K m) 1)
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap ρ (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1) y
          (b ⊗ₜ gA)) = b • gB := by
    intro b
    rw [AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap_tmul, LinearMap.map_smul]
    congr 1
    refine (MiyaokaMori.RelativeProjTwistLocalIso.moduleStalkMap_transpose_unit_germ ρ
      (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1) (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K m) 1)
      (Proj.twistToPushforward (hyperplaneGradedHom K m) (irrelevant_le_map_hyperplaneGradedHom K m) 1) y U hxU eA).trans ?_
    exact congrArg _ (twistToPushforward_app_homogeneousSection (hyperplaneGradedHom K m)
      (irrelevant_le_map_hyperplaneGradedHom K m) 1 (X j.castSucc) (X_mem_one K m _) U)
  have hpure : ∀ ξ : AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensor ρ
      (Proj.twist (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1) y, ∃ b, ξ = b ⊗ₜ gA := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
    | tmul b μ =>
      obtain ⟨c, rfl⟩ := (hfA.stalkEquiv hxU).surjective μ
      refine ⟨c • b, ?_⟩
      rw [IsFrame.stalkEquiv_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add ξ₁ ξ₂ h₁ h₂ =>
      obtain ⟨b₁, rfl⟩ := h₁
      obtain ⟨b₂, rfl⟩ := h₂
      exact ⟨b₁ + b₂, (TensorProduct.add_tmul _ _ _).symm⟩
  constructor
  · intro ξ₁ ξ₂ h
    obtain ⟨b₁, rfl⟩ := hpure ξ₁
    obtain ⟨b₂, rfl⟩ := hpure ξ₂
    simp only [Function.comp_apply, key] at h
    have : hfB.stalkEquiv hyV b₁ = hfB.stalkEquiv hyV b₂ := by
      rw [IsFrame.stalkEquiv_apply, IsFrame.stalkEquiv_apply]; exact h
    rw [(hfB.stalkEquiv hyV).injective this]
  · intro ν
    obtain ⟨b, hb⟩ := (hfB.stalkEquiv hyV).surjective ν
    refine ⟨b ⊗ₜ gA, ?_⟩
    simp only [Function.comp_apply, key]
    rw [← hb, IsFrame.stalkEquiv_apply]

end ProjBundleFiberDegreeOne

end
