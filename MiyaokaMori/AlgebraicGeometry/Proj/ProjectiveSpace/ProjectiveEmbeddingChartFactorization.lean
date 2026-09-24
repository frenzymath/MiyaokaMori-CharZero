import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedEmbeddingIdealCharts
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveCoordinateRatio
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverChartRatio

/-!
# Factoring a projective chart map through the original closed target

For the original projective embedding, its section map on a standard affine chart
is surjective and has exactly the existing transported scheme-theoretic kernel.
A chart evaluation annihilating that kernel therefore descends to sections on the
actual inverse-image open of the original target. Its spectrum map gives a lift
into that same open, with an equality of scheme morphisms over the projective chart.

Everything is keyed on the closed immersion `{X : Scheme} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)
[IsClosedImmersion emb]` (the instance is a section variable from `ker_sectionMap` on; `sectionMap` itself
needs no closed immersion).

Source: Theorem 4.2 of the paper (§4). The kernel inclusion here is a hypothesis
of this local statement: in the realization theorem it is supplied by the equations of `X` and their
vanishing. This file does not identify a new quotient model with the target.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj.ProjectiveEmbeddingChartFactorization

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)

attribute [local instance] MvPolynomial.gradedAlgebra

-- `ProjectiveSpaceOver.chart` / `standardAffineOpen` are ordinary `def`s: `(ProjectiveSpaceOver.chart N k i).toScheme`
-- and `(Proj.basicOpen …).toScheme`, resp. `↑(ProjectiveEmbedding.standardAffineOpen k N i)` and
-- `ProjectiveSpaceOver.chart N k i`, are equal only at default transparency, so `rw`/`simp` on goals containing such
-- composites fail ("motive is not type correct" at implicit transparency). We make the two `def`s reducible in this
-- file only.
set_option allowUnsafeReducibility true in
attribute [local reducible] ProjectiveSpaceOver.chart ProjectiveEmbedding.standardAffineOpen
  ProjectiveSpaceOver

/-- The genuine section map of the original embedding, expressed in its canonical
homogeneous-localization chart coordinates. -/
def sectionMap (i : Fin (N + 1)) :
    ProjectiveEmbedding.chartRing k N i →+* Γ(X, emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i) :=
  (emb.app (ProjectiveSpaceOver.chart N k i)).hom.comp (ProjectiveEmbedding.chartIso k N i).hom.hom

variable [IsClosedImmersion emb]

/-- The section-map kernel is the original scheme-theoretic chart ideal. -/
theorem ker_sectionMap (i : Fin (N + 1)) :
    RingHom.ker (sectionMap emb i) = ProjectiveEmbedding.chartKernelAway emb i := by
  change RingHom.ker ((emb.app (ProjectiveSpaceOver.chart N k i)).hom.comp
      (ProjectiveEmbedding.chartIso k N i).hom.hom) =
    (emb.ker.ideal (ProjectiveEmbedding.standardAffineOpen k N i)).comap (ProjectiveEmbedding.chartIso k N i).hom.hom
  rw [Scheme.Hom.ker_apply, RingHom.comap_ker]

/-- Closed immersion gives surjectivity on this actual affine chart; no independent
surjectivity assumption is added to the embedding. -/
theorem sectionMap_surjective (i : Fin (N + 1)) :
    Function.Surjective (sectionMap emb i) := by
  intro y
  obtain ⟨z, rfl⟩ := emb.app_surjective (ProjectiveSpaceOver.chart N k i)
    (ProjectiveEmbedding.standardAffineOpen k N i).2 y
  refine ⟨(ProjectiveEmbedding.chartIso k N i).inv z, ?_⟩
  -- `CommRingCat.Hom.hom` and `ConcreteCategory.hom` are spelled differently, so the two `simp` lemmas do not
  -- see each other's output; apply `inv_hom_id` through `congrArg` directly.
  have h := congrArg (emb.app (ProjectiveSpaceOver.chart N k i)).hom
    ((ProjectiveEmbedding.chartIso k N i).inv_hom_id_apply z)
  exact h

/-- The inverse image of the standard affine chart is affine because the original
embedding is a closed immersion. This is a property of the original open. -/
theorem preimage_isAffineOpen (i : Fin (N + 1)) :
    IsAffineOpen (emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i) := by
  exact (ProjectiveEmbedding.standardAffineOpen k N i).2.preimage emb

variable (T : Scheme.{u})
    (θ : MvPolynomial (Fin (N + 1)) k →+* Γ(T, ⊤))
    (i : Fin (N + 1)) (hi : IsUnit (θ (MvPolynomial.X i)))
    (hker : ProjectiveEmbedding.chartKernelAway emb i ≤
      RingHom.ker (ProjectiveSpaceOverChart.chartEvaluation N θ i hi))

/-- Descend the existing chart evaluation along the original surjective section map.
Its codomain is the original source's sections, and its domain is sections on the
actual inverse-image chart of the original closed target. -/
def descendedEvaluation :
    Γ(X, emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i) →+* Γ(T, ⊤) :=
  (sectionMap emb i).liftOfSurjective (sectionMap_surjective emb i)
    ⟨ProjectiveSpaceOverChart.chartEvaluation N θ i hi,
      by rw [ker_sectionMap]; exact hker⟩

/-- The descended map agrees with the original chart evaluation after the actual
section map. This retains all structure-sheaf information. -/
theorem descendedEvaluation_comp :
    (descendedEvaluation emb T θ i hi hker).comp (sectionMap emb i) =
      ProjectiveSpaceOverChart.chartEvaluation N θ i hi := by
  exact RingHom.liftOfSurjective_comp (sectionMap emb i) (sectionMap_surjective emb i) _

/-- The resulting scheme lift lands in the actual inverse-image open of `X`. -/
def chartLift : T ⟶ (emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i).toScheme :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (descendedEvaluation emb T θ i hi hker)) ≫
    (preimage_isAffineOpen emb i).isoSpec.inv

private theorem preimageIso_inv_restrict (i : Fin (N + 1)) :
    (preimage_isAffineOpen emb i).isoSpec.inv ≫
        emb ∣_ ProjectiveSpaceOver.chart N k i ≫
          (Proj.basicOpenIsoSpec (projectiveGrading k N) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).hom =
      Spec.map (CommRingCat.ofHom (sectionMap emb i)) := by
  have hchart :
      (Proj.basicOpenIsoSpec (projectiveGrading k N) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).hom =
        (ProjectiveSpaceOver.chart N k i).toSpecΓ ≫ Spec.map (ProjectiveEmbedding.chartIso k N i).hom := rfl
  rw [hchart, ← Category.assoc (emb ∣_ ProjectiveSpaceOver.chart N k i),
    ← Scheme.Opens.toSpecΓ_naturality emb (ProjectiveSpaceOver.chart N k i)]
  simp only [Category.assoc, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]
  -- `← Spec.map_comp` does not match here (the codomain of `(ProjectiveEmbedding.chartIso k N i).hom` is spelled
  -- `Γ(_, ↑(ProjectiveEmbedding.standardAffineOpen k N i))`, only defeq to `Γ(_, ProjectiveSpaceOver.chart N k i)`);
  -- instead split the right-hand side into a composite in `CommRingCat` and use `Spec.map_comp` forwards.
  have hcomp : CommRingCat.ofHom (sectionMap emb i) =
      (ProjectiveEmbedding.chartIso k N i).hom ≫ emb.app (ProjectiveSpaceOver.chart N k i) := rfl
  rw [hcomp]
  exact (Spec.map_comp _ _).symm

/-- The lift composed with the restriction of the original embedding is exactly
the existing canonical chart map, as a morphism of schemes. -/
theorem chartLift_restrict :
    chartLift emb T θ i hi hker ≫ emb ∣_ ProjectiveSpaceOver.chart N k i =
      ProjectiveSpaceOverChart.chartMap T N θ i hi := by
  let q := Proj.basicOpenIsoSpec (projectiveGrading k N) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one
  apply (cancel_mono q.hom).mp
  have hspec :
      Spec.map (CommRingCat.ofHom (descendedEvaluation emb T θ i hi hker)) ≫
          Spec.map (CommRingCat.ofHom (sectionMap emb i)) =
        Spec.map (CommRingCat.ofHom
          (ProjectiveSpaceOverChart.chartEvaluation N θ i hi)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, descendedEvaluation_comp]
  simp only [chartLift, ProjectiveSpaceOverChart.chartMap, q, Category.assoc,
    preimageIso_inv_restrict, hspec, Iso.inv_hom_id, Category.comp_id]

/-- The local factorization into the original target, with its original open inclusion. -/
def lift : T ⟶ X :=
  chartLift emb T θ i hi hker ≫ (emb ⁻¹ᵁ ProjectiveSpaceOver.chart N k i).ι

/-- Composing with the original closed embedding recovers the original chart map. -/
theorem lift_embedding :
    lift emb T θ i hi hker ≫ emb =
      ProjectiveSpaceOverChart.chartMap T N θ i hi ≫ (ProjectiveSpaceOver.chart N k i).ι := by
  rw [lift, Category.assoc,
    ← morphismRestrict_ι emb (ProjectiveSpaceOver.chart N k i), ← Category.assoc,
    chartLift_restrict]

include hi in
/-- Invertibility of the selected coordinate supplies the irrelevant-ideal
condition for the canonical projective morphism on this chart. -/
theorem irrelevant_map_eq_top :
    (HomogeneousIdeal.irrelevant (projectiveGrading k N)).toIdeal.map θ = ⊤ := by
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem θ
      (HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading k N)
        Nat.zero_lt_one (MvPolynomial.isHomogeneous_X k i))) hi

/-- The local factorization also recovers Mathlib's canonical projectivization;
its irrelevant-ideal condition is derived from the selected unit coordinate. -/
theorem lift_embedding_fromOfGlobalSections :
    lift emb T θ i hi hker ≫ emb =
      Proj.fromOfGlobalSections (projectiveGrading k N) θ
        (irrelevant_map_eq_top T θ i hi) := by
  rw [lift_embedding]
  exact ProjectiveSpaceOverChart.chartMap_ι T N θ
    (irrelevant_map_eq_top T θ i hi) i hi

/-- Any other factorization of the same chart map into the original target equals
this one. The uniqueness is supplied by the original closed immersion. -/
theorem lift_unique (g : T ⟶ X)
    (hg : g ≫ emb =
      ProjectiveSpaceOverChart.chartMap T N θ i hi ≫ (ProjectiveSpaceOver.chart N k i).ι) :
    g = lift emb T θ i hi hker := by
  exact (cancel_mono emb).mp (hg.trans (lift_embedding emb T θ i hi hker).symm)

end AlgebraicGeometry.Proj.ProjectiveEmbeddingChartFactorization
