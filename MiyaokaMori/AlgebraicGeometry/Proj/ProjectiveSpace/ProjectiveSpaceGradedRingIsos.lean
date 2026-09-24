import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjMapToSpecZero
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra

/-! # Comparison isomorphisms of projective spaces from graded ring isomorphisms

Two comparison isomorphisms of projective spaces, both compatible with the structure morphisms
to the base `Spec`, obtained from graded ring isomorphisms of the homogeneous coordinate rings
via `Proj.isoOfGradedRingEquiv` (below; `Proj.map` in both directions) and
`AlgebraicGeometry.Proj.proj_map_toSpecZero` (Stacks 01MX: `Proj.map` is compatible with `Proj.toSpecZero`):

* `weightedProjectiveSpace_one_iso_projectiveSpace`: the weighted projective space with all weights
  `1` on `N + 1` variables is `P^N` (the standard grading on `k[x_0, …, x_N]` is the weight-`1`
  grading, `MvPolynomial.weightedHomogeneousSubmodule_one`, and `rename` along the bijection
  `ULift (Fin (N+1)) ≃ Fin (N+1)` preserves degrees);
* `projectiveSpace_iso_of_ringIso`: a ring isomorphism `K ≅ k` of fields induces
  `P^N_K ≅ P^N_k` over `Spec K ≅ Spec k` (`MvPolynomial.map` of an isomorphism preserves
  homogeneity in both directions).

Also the general compatibility `Proj.isoOfGradedRingEquiv_hom_toSpecZero`.
`Proj.isoOfGradedRingEquiv` is the same construction as `Proj.isoOfRingEquiv` in
`LocallyWeightedProjLocalProduct`; it is repeated here, with `hom`/`inv` exposed as `Proj.map` of
named graded ring homomorphisms, because that module has a much larger import closure.

Sources: Stacks 01MX (functoriality of Proj and the map to `Spec` of the degree-0 part);
Corollary 4.3 of the paper (the fibres of `P(O ⊕ L) → C` are `P¹`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
variable [GradedRing 𝒜] [GradedRing ℬ]

/-- The graded ring homomorphism `𝒜 →+*ᵍ ℬ` induced by a degree-preserving ring equivalence. -/
def gradedRingHomOfRingEquiv (e : A ≃+* B) (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) :
    𝒜 →+*ᵍ ℬ where
  toRingHom := e.toRingHom
  map_mem := fun {i} {a} ha => (he i a).mp ha

/-- The graded ring homomorphism `ℬ →+*ᵍ 𝒜` induced by the inverse equivalence; it underlies
`(isoOfGradedRingEquiv e he).hom : Proj 𝒜 ⟶ Proj ℬ`. -/
def gradedRingHomOfRingEquivSymm (e : A ≃+* B) (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) :
    ℬ →+*ᵍ 𝒜 where
  toRingHom := e.symm.toRingHom
  map_mem := fun {i} {b} hb => (he i (e.symm b)).mpr (by simpa using hb)

theorem irrelevant_le_map_gradedRingHomOfRingEquiv (e : A ≃+* B)
    (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) :
    HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (gradedRingHomOfRingEquiv e he) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi b hb
  change b ∈ ℬ i at hb
  rw [← show gradedRingHomOfRingEquiv e he (e.symm b) = b by
    simp [gradedRingHomOfRingEquiv]]
  apply Ideal.mem_map_of_mem (gradedRingHomOfRingEquiv e he).toRingHom
  exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi ((he i (e.symm b)).mpr (by simpa using hb))

theorem irrelevant_le_map_gradedRingHomOfRingEquivSymm (e : A ≃+* B)
    (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) :
    HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant ℬ).map (gradedRingHomOfRingEquivSymm e he) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  change a ∈ 𝒜 i at ha
  rw [← show gradedRingHomOfRingEquivSymm e he (e a) = a by
    simp [gradedRingHomOfRingEquivSymm]]
  apply Ideal.mem_map_of_mem (gradedRingHomOfRingEquivSymm e he).toRingHom
  exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi ((he i a).mp ha)

/-- A degree-preserving ring equivalence induces an isomorphism of Proj schemes
(`hom = Proj.map` of the inverse, `inv = Proj.map` of the equivalence; Stacks 01MX). -/
def isoOfGradedRingEquiv (e : A ≃+* B) (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) :
    Proj 𝒜 ≅ Proj ℬ where
  hom := Proj.map (gradedRingHomOfRingEquivSymm e he) (irrelevant_le_map_gradedRingHomOfRingEquivSymm e he)
  inv := Proj.map (gradedRingHomOfRingEquiv e he) (irrelevant_le_map_gradedRingHomOfRingEquiv e he)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have hgf : (gradedRingHomOfRingEquivSymm e he).comp (gradedRingHomOfRingEquiv e he) =
        GradedRingHom.id 𝒜 := by
      ext a
      simp [gradedRingHomOfRingEquiv, gradedRingHomOfRingEquivSymm]
    have hmap : Proj.map ((gradedRingHomOfRingEquivSymm e he).comp (gradedRingHomOfRingEquiv e he))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_gradedRingHomOfRingEquiv e he)
          (irrelevant_le_map_gradedRingHomOfRingEquivSymm e he)) =
        Proj.map (GradedRingHom.id 𝒜) (by simp) := by
      congr 1
    exact hmap.trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    have hfg : (gradedRingHomOfRingEquiv e he).comp (gradedRingHomOfRingEquivSymm e he) =
        GradedRingHom.id ℬ := by
      ext b
      simp [gradedRingHomOfRingEquiv, gradedRingHomOfRingEquivSymm]
    have hmap : Proj.map ((gradedRingHomOfRingEquiv e he).comp (gradedRingHomOfRingEquivSymm e he))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_gradedRingHomOfRingEquivSymm e he)
          (irrelevant_le_map_gradedRingHomOfRingEquiv e he)) =
        Proj.map (GradedRingHom.id ℬ) (by simp) := by
      congr 1
    exact hmap.trans Proj.map_id

/-- Compatibility of `isoOfGradedRingEquiv` with the degree-zero structure maps (Stacks 01MX). -/
theorem isoOfGradedRingEquiv_hom_toSpecZero (e : A ≃+* B)
    (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) :
    (isoOfGradedRingEquiv e he).hom ≫ Proj.toSpecZero ℬ =
      Proj.toSpecZero 𝒜 ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (gradedRingHomOfRingEquivSymm e he).gradedZeroRingHom) :=
  AlgebraicGeometry.Proj.proj_map_toSpecZero _ _

end AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

/-- The weighted projective space with all weights `1` on `ULift (Fin (N + 1))` is `P^N_K`,
compatibly with the structure morphisms to `Spec K`. Both are `Proj` of a polynomial ring in
`N + 1` variables: the weight-`1` grading is the standard grading (`weightedHomogeneousSubmodule_one`,
definitionally) and `rename` along `Equiv.ulift` preserves homogeneity
(`IsHomogeneous.rename_isHomogeneous_iff`); the structure maps agree because `rename` fixes
constants (`rename_C`). -/
theorem weightedProjectiveSpace_one_iso_projectiveSpace (K : Type u) [Field K] (N : ℕ) :
    ∃ e : weightedProjectiveSpace K (fun _ : ULift.{u} (Fin (N + 1)) => 1) (fun _ => Nat.one_pos) ≅
        ProjectiveSpace N K,
      e.hom ≫ (ProjectiveSpace N K ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
        (weightedProjectiveSpace K (fun _ : ULift.{u} (Fin (N + 1)) => 1) (fun _ => Nat.one_pos) ↘
          AlgebraicGeometry.Spec (CommRingCat.of K)) := by
  classical
  let ε : MvPolynomial (ULift.{u} (Fin (N + 1))) K ≃+* MvPolynomial (Fin (N + 1)) K :=
    (MvPolynomial.renameEquiv K (Equiv.ulift : ULift.{u} (Fin (N + 1)) ≃ Fin (N + 1))).toRingEquiv
  have hε : ∀ i (a : MvPolynomial (ULift.{u} (Fin (N + 1))) K),
      a ∈ MiyaokaMori.WeightedJets.weightedPolynomialGrading K
          (fun _ : ULift.{u} (Fin (N + 1)) => (⟨1, Nat.one_pos⟩ : ℕ+)) i ↔
        ε a ∈ AlgebraicGeometry.Proj.projectiveGrading K N i := by
    intro i a
    change MvPolynomial.IsWeightedHomogeneous _ a i ↔
      MvPolynomial.IsHomogeneous (MvPolynomial.rename (Equiv.ulift : ULift.{u} (Fin (N + 1)) ≃ Fin (N + 1)) a) i
    rw [MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Equiv.ulift.injective]
    rfl
  refine ⟨AlgebraicGeometry.Proj.isoOfGradedRingEquiv ε hε, ?_⟩
  change (AlgebraicGeometry.Proj.isoOfGradedRingEquiv ε hε).hom ≫
      (AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K _))) =
    AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K _))
  rw [← CategoryTheory.Category.assoc, AlgebraicGeometry.Proj.isoOfGradedRingEquiv_hom_toSpecZero,
    CategoryTheory.Category.assoc, ← AlgebraicGeometry.Spec.map_comp]
  congr 2
  ext c
  simp [AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm, ε]

/-- A ring isomorphism `φ : K ≅ k` of fields induces `P^N_K ≅ P^N_k`, compatibly with the
structure morphisms: `e.hom ≫ (P^N_k → Spec k) = (P^N_K → Spec K) ≫ Spec.map φ.inv`.
The isomorphism is `Proj` of `MvPolynomial.map φ` (homogeneity is preserved in both directions,
`IsHomogeneous.map` / `IsHomogeneous.of_map`), and the structure maps agree because
`map φ` acts on constants by `φ`. -/
theorem projectiveSpace_iso_of_ringIso (N : ℕ) {K k : Type u} [Field K] [Field k]
    (φ : CommRingCat.of K ≅ CommRingCat.of k) :
    ∃ e : ProjectiveSpace N K ≅ ProjectiveSpace N k,
      e.hom ≫ (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (ProjectiveSpace N K ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) ≫
          AlgebraicGeometry.Spec.map φ.inv := by
  classical
  let ε : MvPolynomial (Fin (N + 1)) K ≃+* MvPolynomial (Fin (N + 1)) k :=
    MvPolynomial.mapEquiv (Fin (N + 1)) φ.commRingCatIsoToRingEquiv
  have hε : ∀ i (a : MvPolynomial (Fin (N + 1)) K),
      a ∈ AlgebraicGeometry.Proj.projectiveGrading K N i ↔ ε a ∈ AlgebraicGeometry.Proj.projectiveGrading k N i := by
    intro i a
    change MvPolynomial.IsHomogeneous a i ↔
      MvPolynomial.IsHomogeneous (MvPolynomial.map (φ.commRingCatIsoToRingEquiv : K →+* k) a) i
    exact ⟨fun h => h.map _, fun h => h.of_map φ.commRingCatIsoToRingEquiv.injective⟩
  refine ⟨AlgebraicGeometry.Proj.isoOfGradedRingEquiv ε hε, ?_⟩
  change (AlgebraicGeometry.Proj.isoOfGradedRingEquiv ε hε).hom ≫
      (AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k _))) =
    (AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K _))) ≫
      AlgebraicGeometry.Spec.map φ.inv
  rw [← CategoryTheory.Category.assoc, AlgebraicGeometry.Proj.isoOfGradedRingEquiv_hom_toSpecZero,
    CategoryTheory.Category.assoc, ← AlgebraicGeometry.Spec.map_comp,
    CategoryTheory.Category.assoc, ← AlgebraicGeometry.Spec.map_comp]
  congr 2
  ext c
  have hφ : ∀ c : k, φ.commRingCatIsoToRingEquiv.symm c = φ.inv.hom c := fun _ => rfl
  simp [AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm, ε, hφ]

end
