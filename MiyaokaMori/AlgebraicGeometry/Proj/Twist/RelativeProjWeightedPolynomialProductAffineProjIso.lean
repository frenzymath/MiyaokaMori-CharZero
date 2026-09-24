import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceGradedRingIsos
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLocalIso

/-! # The twist comparison along a graded ring isomorphism is an isomorphism

Stacks 01MX for a graded ring **isomorphism**: for a degree-preserving ring equivalence `e : A ≃+* B`
of graded rings, the comparison map `θ = Proj.twistPullbackHom e⁻¹ n` of the twisting sheaves along
the isomorphism `Proj.isoOfGradedRingEquiv e he : Proj 𝒜 ≅ Proj ℬ` (whose `hom` is `Proj.map e⁻¹`) is
an isomorphism.

The Proj isomorphism itself is `AlgebraicGeometry.Proj.isoOfGradedRingEquiv` from
`ProjectiveSpaceGradedRingIsos`, together with its graded ring homomorphisms `gradedRingHomOfRingEquiv` /
`gradedRingHomOfRingEquivSymm` and the compatibility `isoOfGradedRingEquiv_hom_toSpecZero`; it is reused
here (the same construction also exists as `Proj.isoOfRingEquiv` in `LocallyWeightedProjLocalProduct`,
which is too high in the import graph for `RelativeProjWeightedPolynomialProductAffine`).

The `θ` statement is the special case of `Proj.isIso_twistPullbackHom_of_bijective`
(`LocallyWeightedProjLocalProduct`) in which the bijective graded homomorphism comes from a ring
equivalence; here it is proved from `isIso_twistPullbackHom_of_isLocalizationAway`
(`RelativeProjTwistLocalIso`): a ring isomorphism is the localization at the unit `1 ∈ ℬ 0`
(`IsLocalization.away_of_isUnit_of_bijective`), and `Proj.map` of it is an isomorphism, hence an open
immersion. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
variable (e : A ≃+* B) (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i)

theorem isoOfGradedRingEquiv_hom' :
    (isoOfGradedRingEquiv e he).hom =
      Proj.map (gradedRingHomOfRingEquivSymm e he) (irrelevant_le_map_gradedRingHomOfRingEquivSymm e he) := rfl

/-- `Proj.map e⁻¹ : Proj 𝒜 ⟶ Proj ℬ` is an isomorphism (it is `(isoOfGradedRingEquiv e he).hom`). -/
theorem isIso_map_gradedRingHomOfRingEquivSymm :
    IsIso (Proj.map (gradedRingHomOfRingEquivSymm e he) (irrelevant_le_map_gradedRingHomOfRingEquivSymm e he)) :=
  (isoOfGradedRingEquiv e he).isIso_hom

/-- **Stacks 01MX for an isomorphism**: the twisting-sheaf comparison map `θ` along
`Proj.map e⁻¹ : Proj 𝒜 ⟶ Proj ℬ` is an isomorphism. Proof: `e⁻¹ : B → A` is the localization of `B` at
the unit `1 ∈ ℬ 0` (`IsLocalization.away_of_isUnit_of_bijective`) and `Proj.map e⁻¹` is an isomorphism,
hence an open immersion; apply `isIso_twistPullbackHom_of_isLocalizationAway`. -/
theorem isIso_twistPullbackHom_gradedRingHomOfRingEquivSymm (n : ℤ) :
    IsIso (Proj.twistPullbackHom (gradedRingHomOfRingEquivSymm e he)
      (irrelevant_le_map_gradedRingHomOfRingEquivSymm e he) n) := by
  haveI := isIso_map_gradedRingHomOfRingEquivSymm e he
  refine MiyaokaMori.RelativeProjTwistLocalIso.isIso_twistPullbackHom_of_isLocalizationAway
    (gradedRingHomOfRingEquivSymm e he) (irrelevant_le_map_gradedRingHomOfRingEquivSymm e he)
    (f := (1 : B)) (SetLike.one_mem_graded ℬ) ?_ n
  letI := (gradedRingHomOfRingEquivSymm e he).toRingHom.toAlgebra
  exact IsLocalization.away_of_isUnit_of_bijective A isUnit_one e.symm.bijective

end AlgebraicGeometry.Proj

end
