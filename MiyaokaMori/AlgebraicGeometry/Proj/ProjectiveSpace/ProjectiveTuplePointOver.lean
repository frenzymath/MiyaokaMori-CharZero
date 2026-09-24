import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTuplePoint

/-! # The tuple point is a morphism over `k`

The `R`-point `[b_0 : … : b_N] : Spec R → P^N_k` is a `k`-morphism: composed with the
structure morphism it equals `Spec (k → R)`.

Reference: Hartshorne II Thm 7.1 (morphisms over the base); compare the field case
`AlgebraicGeometry.Proj.ProjectiveCoordinateRatio.fieldTupleMorphism`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `tuplePoint ≫ (P^N ↘ Spec k) = Spec.map c`.

Proof sketch: the structure morphism `ProjectiveSpace N k ↘ Spec k` unfolds to
`Proj.toSpecZero _ ≫ Spec.map (ofHom (algebraMap k (𝒜 0)))` (`ProjectiveSpace.toSpecBase`).
By `Proj.fromOfGlobalSections_toSpecZero` it remains to check the ring-homomorphism identity
`(tupleEval ∘ algebraMap (𝒜 0) → k[X]) ∘ algebraMap k (𝒜 0) = ΓSpecIso.inv ∘ c`
(`MvPolynomial.eval₂Hom_C`), and to finish with the inverse pair `Scheme.toSpecΓ` / `ΓSpecIso`
(`AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv`). The `GradedRing (projectiveGrading k N)`
instance required by `Proj.fromOfGlobalSections_toSpecZero` is the local instance
`MvPolynomial.gradedAlgebra` above. When `R` is the zero ring, `hb` holds trivially, `Spec R`
is empty, and the same proof applies (it does not use `R ≠ 0`). -/
theorem ProjectiveSpace.tuplePoint_over (k : Type u) [Field k] (N : ℕ) (R : Type u) [CommRing R]
    (c : k →+* R) (b : Fin (N + 1) → R) (hb : Ideal.span (Set.range b) = ⊤) :
    ProjectiveSpace.tuplePoint k N R c b hb ≫
        (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom c) := by
  change AlgebraicGeometry.Proj.fromOfGlobalSections _ _ _ ≫
    (AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map _) = _
  rw [← Category.assoc, AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero, Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have heval : ((ProjectiveSpace.tupleEval k N R c b).comp
      (algebraMap ((AlgebraicGeometry.Proj.projectiveGrading k N) 0) (MvPolynomial (Fin (N + 1)) k))).comp
        (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0)) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp c := by
    ext x
    simp [ProjectiveSpace.tupleEval]
  rw [heval, CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp, ← Category.assoc]
  change ((AlgebraicGeometry.Spec (CommRingCat.of R)).toSpecΓ ≫
    AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv) ≫ _ = _
  rw [AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

end
