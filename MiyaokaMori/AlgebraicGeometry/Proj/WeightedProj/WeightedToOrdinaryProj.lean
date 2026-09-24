import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedToOrdinaryProjCharts

/-! # The finite surjection from ordinary to weighted projective space

`[u_{i,q}] ↦ [u_{i,q}^q]` is a finite surjective morphism from ordinary to weighted projective
space (Dolgachev, *Weighted projective varieties*, 1.2.2), used in the proof of the affine lift after
finite base change (Lemma 3.1) and of the Veronese polarization lemma of the paper.

Proof (Stacks 01MY + charts). Let `ψ : k[x] (weights w) → k[u] (weights 1)`, `x_i ↦ u_i^{w_i}`, and
`g = powerMap` the induced morphism `P^{|σ|-1} → P(w)` (`WeightedToOrdinaryProjCharts`).
`P(w)` is covered by the affine opens `D₊(x_i) = Spec k[x]_(x_i)` (`Proj.affineOpenCoverOfIrrelevantLESpan`,
the `x_i` span the irrelevant ideal). The chart square
`Spec k[u]_(u_i^{w_i}) → Spec k[x]_(x_i)` / `awayι` / `awayι` / `g` is a pullback
(`isPullback_awayι_powerMap`), and its top arrow is `Spec` of the ring map
`weightedPowerAwayMap`, which is finite and injective (`weightedPowerAwayMap_finite_injective`).
Finiteness and surjectivity are Zariski-local on the target
(`IsZariskiLocalAtTarget.of_openCover`), so it suffices to check them on `Spec` of these ring maps:
finite by `IsFinite.SpecMap_iff`; surjective by lying over for the integral (finite) injective
ring map (`RingHom.IsIntegral.comap_surjective`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- `letI` (not `let`) is needed in proofs: it inlines the graded-ring instance so that terms match
-- the statements syntactically (a `let`-bound instance fvar breaks `rw`).
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace WeightedToOrdinaryProj

variable (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)

/-- The irrelevant ideal of `k[x]` with positive weights `w` is contained in `(x_i)_i`:
a weighted homogeneous polynomial of positive weighted degree has no constant term
(`irrelevant_le_span_X` of `WeightedToOrdinaryProjCharts` is the case `w = 1`). -/
theorem irrelevant_le_span_X' :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    (HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule k w)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  change p ∈ Ideal.span _
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hp' : p.IsWeightedHomogeneous w i := hp
  have hwt := hp' (MvPolynomial.mem_support_iff.mp hm)
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun j => h j (Set.mem_univ j)
  subst hm0
  simp at hwt
  omega

/-- The affine open cover of `P(w)` by the charts `D₊(x_i) = Spec k[x]_(x_i)`. -/
def targetCover :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    (AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k w)).OpenCover :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  (AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan
    (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X : σ → MvPolynomial σ k)
    (m := w) (X_mem k w) hw (irrelevant_le_span_X' k w)).openCover

/-- The chart ring map `k[x]_(x_i) → k[u]_(u_i^{w_i})` has surjective `Spec`: it is finite
(`weightedPowerAwayMap_finite_injective`), hence integral, and injective, so lying over applies. -/
theorem spec_weightedPowerAwayMap_surjective (i : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    AlgebraicGeometry.Surjective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i))) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  obtain ⟨hfin, hinj⟩ := weightedPowerAwayMap_finite_injective k w hw i
  constructor
  exact hfin.to_isIntegral.comap_surjective hinj

/-- A Zariski-local-on-target property holds for `powerMap` as soon as it holds for
`Spec (weightedPowerAwayMap k w hw i)` for every `i` (chart squares are pullbacks). -/
theorem powerMap_of_charts (P : MorphismProperty AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    (H : ∀ i : σ,
      letI := MvPolynomial.weightedGradedAlgebra (R := k) w
      letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
      P (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i)))) :
    P (powerMap k w hw) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  refine AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover (P := P) (targetCover k w hw)
    fun i => ?_
  -- `i : (targetCover k w hw).I₀` is `σ` by unfolding, and `(targetCover k w hw).f i` is the chart
  -- `awayι 𝒜 (X i)`; the pullback of `powerMap` along it is (up to the iso `isoPullback`) the chart
  -- square's top arrow `Spec (weightedPowerAwayMap k w hw i)`.
  have hpb := (isPullback_awayι_powerMap k w hw (i : σ)).flip
  refine (P.cancel_left_of_respectsIso hpb.isoPullback.hom _).mp ?_
  have key : hpb.isoPullback.hom ≫ (targetCover k w hw).pullbackHom (powerMap k w hw) i =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw (i : σ))) :=
    hpb.isoPullback_hom_snd
  exact (congrArg (fun g => P g) key).mpr (H (i : σ))

end WeightedToOrdinaryProj

-- `IsZariskiLocalAtTarget @IsFinite` (from Mathlib's `HasAffineProperty @IsFinite`) is only found by
-- instance search with this Mathlib-internal flag (as in Mathlib's own `Morphisms/Basic.lean`);
-- without it the `HasAffineProperty` instance of `IsFinite` fails to unify.
set_option backward.isDefEq.respectTransparency false in
open WeightedToOrdinaryProj in
/-- There is a finite surjective morphism `P^{|σ|-1} → P(w)`, namely the power map `[u] ↦ [u^w]`. -/
theorem finite_surjective_toWeightedProj (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ g : weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos)
            ⟶ weightedProjectiveSpace k w hw,
      AlgebraicGeometry.IsFinite g ∧ Function.Surjective g.base ∧
      /- `g` is induced by the graded ring homomorphism `x_i ↦ x_i^{w i}` -/
      InducedByPowerMap g := by
  refine ⟨powerMap k w hw, ?_, ?_, inducedByPowerMap_powerMap k w hw⟩
  · refine powerMap_of_charts k w hw @AlgebraicGeometry.IsFinite fun i => ?_
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    exact (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr
      (weightedPowerAwayMap_finite_injective k w hw i).1
  · have h : AlgebraicGeometry.Surjective (powerMap k w hw) :=
      powerMap_of_charts k w hw @AlgebraicGeometry.Surjective
        (spec_weightedPowerAwayMap_surjective k w hw)
    exact h.surj

end
