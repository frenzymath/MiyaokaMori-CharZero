import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedEmbeddingIdealCharts
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverChartRatio
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Homogeneous ideal successor for a projective embedding

This file isolates the actual polynomial equation candidate for a closed immersion
`emb : X ⟶ P^N_k`.  The chart ideals come from the scheme-theoretic kernels
on `D₊(Xᵢ)` (`ProjectiveEmbedding.chartKernelAway`); they are not the kernels
of the seed evaluation map in `SeedAmbientConeEquationCharts`.

The intersection and homogeneous core below are explicit constructions. The
localization and Proj-recovery properties that would make the core the ideal of
`X` are stated as separate `Prop`-valued contracts; the localization equality is
proved in `SeedHomogeneousConeReverse`, the Proj-recovery contract is not used
downstream.  No definition chooses a homogeneous ideal from an existential
theorem, and no cone object is defined from the seed-evaluation kernel.

The polynomial ring and grading are written `MvPolynomial (Fin (N + 1)) k` and `projectiveGrading k N`.
The dehomogenization data (`embeddingChartCoefficientMap k N i`, `embeddingChartLocalizationMap k N i`) depend only on
`k`, `N`; the kernel data (`embeddingChartPolynomialKernel emb i`, `embeddingRawPolynomialIdeal emb`,
`embeddingHomogeneousCore emb`, …) take the embedding.

The coordinate ratio `X_j / X_i` in chart `i` is `ProjectiveSpaceOverChart.ratioElement (R := k) N j i`
(`ProjectiveSpaceOverChartRatio`; note the **index order** — `ratioElement n a b` is `T_a / T_b` in chart `b`), and
`chartRing k N i` is `rfl`-equal to its ring `HomogeneousLocalization.Away (homogeneousSubmodule …) (X i)`.
`embeddingChartLocalizationMap k N i` (dehomogenization at `X_i`) is a def written via `ratioElement`;
`embeddingChartLocalizationMap_X` is a lemma about `ratioElement`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ## The polynomial ring and actual chart maps -/

/-- The coefficient map into the degree-zero homogeneous localization chart. -/
def embeddingChartCoefficientMap (N : ℕ) (i : Fin (N + 1)) :
    k →+* ProjectiveEmbedding.chartRing k N i :=
  (HomogeneousLocalization.fromZeroRingHom (projectiveGrading k N)
      (Submonoid.powers (MvPolynomial.X i))).comp
    { toFun := fun r =>
        ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
      map_one' := by ext; simp
      map_mul' := by intro r s; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro r s; ext; simp }

/-- Dehomogenization at `Xᵢ`, sending `Xⱼ` to the actual ratio `Xⱼ/Xᵢ`
(`ProjectiveSpaceOverChart.ratioElement N j i`, the project's coordinate ratio in chart `i`). -/
def embeddingChartLocalizationMap (N : ℕ) (i : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) k →+* ProjectiveEmbedding.chartRing k N i :=
  MvPolynomial.eval₂Hom (embeddingChartCoefficientMap k N i)
    (fun j => ProjectiveSpaceOverChart.ratioElement (R := k) N j i)

@[simp]
theorem embeddingChartLocalizationMap_X (N : ℕ) (i j : Fin (N + 1)) :
    embeddingChartLocalizationMap k N i (MvPolynomial.X j) =
      ProjectiveSpaceOverChart.ratioElement (R := k) N j i := by
  simp [embeddingChartLocalizationMap]

variable {k} {X : Scheme.{u}} {N : ℕ} (emb : X ⟶ ProjectiveSpace N k)

/-- The actual polynomial ideal transported from the scheme-theoretic chart kernel. -/
def embeddingChartPolynomialKernel (i : Fin (N + 1)) : Ideal (MvPolynomial (Fin (N + 1)) k) :=
  (ProjectiveEmbedding.chartKernelAway emb i).comap (embeddingChartLocalizationMap k N i)

/-- The raw global candidate obtained by intersecting all standard chart kernels. -/
def embeddingRawPolynomialIdeal : Ideal (MvPolynomial (Fin (N + 1)) k) :=
  ⨅ i : Fin (N + 1), embeddingChartPolynomialKernel emb i

/-- The largest homogeneous ideal contained in the raw chart-kernel intersection. -/
def embeddingHomogeneousCore : HomogeneousIdeal (projectiveGrading k N) :=
  Ideal.homogeneousCore (projectiveGrading k N) (embeddingRawPolynomialIdeal emb)

/-- The localization of the homogeneous core at the `i`th projective coordinate. -/
def embeddingCoreChartLocalization (i : Fin (N + 1)) : Ideal (ProjectiveEmbedding.chartRing k N i) :=
  Ideal.map (embeddingChartLocalizationMap k N i) (embeddingHomogeneousCore emb).toIdeal

/-! ## Obligations for the actual cone equation ideal -/

/-- Scheme-theoretic equality required on every standard projective chart.

This equality is an equality of ideals, so it retains nilpotents and is
strictly stronger than equality of radicals or supports.
-/
def embeddingCoreLocalizationEquality : Prop :=
  ∀ i : Fin (N + 1),
    embeddingCoreChartLocalization emb i = ProjectiveEmbedding.chartKernelAway emb i

/-- The quotient ring attached to the homogeneous-core candidate. -/
abbrev embeddingCoreQuotient : Type u :=
  MvPolynomial (Fin (N + 1)) k ⧸ (embeddingHomogeneousCore emb).toIdeal

/-- The actual closed-subscheme ring on the `i`th embedding chart. -/
abbrev embeddingClosedChartQuotient (i : Fin (N + 1)) : Type u :=
  ProjectiveEmbedding.chartRing k N i ⧸ ProjectiveEmbedding.chartKernelAway emb i

/-- The canonical quotient map from the ambient embedding chart. -/
def embeddingClosedChartQuotientMap (i : Fin (N + 1)) :
    ProjectiveEmbedding.chartRing k N i →+* embeddingClosedChartQuotient emb i :=
  Ideal.Quotient.mk (ProjectiveEmbedding.chartKernelAway emb i)

/-!
`ProjRecoveryContract` records the data that a proof of Proj recovery must construct.
It is a proposition, not a cone constructor: the existential is not unpacked here, and no
classical witness selection or default witness is used by this file.

The fields require (1) an honest grading on the actual quotient ring, (2) the
graded quotient map whose underlying ring map is `Ideal.Quotient.mk`, (3) the
irrelevant-ideal cover needed by `Proj.map`, (4) affine chart isomorphisms to
the actual closed-subscheme chart quotients, commuting with the canonical
`Away.map` and chart quotient maps, and (5) equality of the resulting Proj
morphism with the original closed immersion.  Together with
`embeddingCoreLocalizationEquality`, the chart equalities are
scheme-theoretic rather than set-theoretic.
-/
def ProjRecoveryContract : Prop :=
  ∃ (𝒬 : ℕ → Submodule k (embeddingCoreQuotient emb))
    (_ : GradedRing 𝒬)
    (q : projectiveGrading k N →+*ᵍ 𝒬)
    (hq : (HomogeneousIdeal.irrelevant 𝒬).toIdeal ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading k N)).toIdeal.map q.toRingHom)
    (x : Proj 𝒬 ≅ X),
    q.toRingHom = Ideal.Quotient.mk (embeddingHomogeneousCore emb).toIdeal ∧
    (∀ i : Fin (N + 1),
      ∃ (chartIso : CommRingCat.of (HomogeneousLocalization.Away 𝒬
          (q (MvPolynomial.X i))) ≅ CommRingCat.of (embeddingClosedChartQuotient emb i)),
        (chartIso.hom.hom).comp (HomogeneousLocalization.Away.map q
          (MvPolynomial.X i)) = embeddingClosedChartQuotientMap emb i) ∧
    x.hom ≫ emb = Proj.map q hq

/-! ## Explicit successor contract -/

/--
The complete successor obligation: the raw/core definitions above must recover
the original embedding on every chart and on Proj.  This is deliberately a
predicate; the theorem establishing it needs denominator clearing and the quotient grading.
-/
def homogeneousConeSuccessorContract : Prop :=
  embeddingCoreLocalizationEquality emb ∧ ProjRecoveryContract emb

end AlgebraicGeometry.Proj
