import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPowerChartFinite
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01my

/-! # Charts of the power map `P^{|σ|-1} → P(w)`

Let `ψ = weightedPowerGradedHom k w : k[x] (weights w) → k[x] (weights 1)`, `x_i ↦ x_i^{w_i}`.
This file proves, for the morphism `powerMap = topIso⁻¹ ≫ isoOfEq ≫ Proj.mapOfGradedHom ψ`:

* `mapDomain_eq_top`: `U(ψ) = Proj k[x]` (Stacks 01MY: `D₊(ψ x_i) = D₊(x_i^{w_i}) = D₊(x_i)` cover);
* `awayι_comp_powerMap`: on `D₊(x_i^{w_i})` the map is `Spec (Away.map ψ x_i)` (Stacks 01MY);
* `powerMap_preimage_basicOpen`: `powerMap⁻¹ D₊(x_i) = D₊(x_i^{w_i})`;
* `isPullback_awayι_powerMap`: the chart square is a pullback.

References: Dolgachev, *Weighted projective varieties*, §1.2.2; Stacks 01MY.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- `letI` (not `let`) is needed in proofs: it inlines the graded-ring instance so that terms match
-- the statements syntactically (a `let`-bound instance fvar breaks `rw`).
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace WeightedToOrdinaryProj

variable (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)

omit [Fintype σ] in
/-- `x_i` is weighted homogeneous of degree `w i` (membership form). -/
theorem X_mem (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ k) ∈ MvPolynomial.weightedHomogeneousSubmodule k w (w i) :=
  MvPolynomial.isWeightedHomogeneous_X k w i

/-- `ψ x_i = x_i^{w_i}` is homogeneous of degree `w i` for the weights `1` (stated with the
`DFunLike` coercion of `ψ`, so that it matches `ψ x` syntactically). -/
theorem psiX_mem (i : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    weightedPowerGradedHom k w (MvPolynomial.X i) ∈
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) (w i) :=
  (weightedPowerGradedHom k w).2 (X_mem k w i)

/-- The irrelevant ideal of `k[x]` (all weights `1`) is contained in `(x_i)_i`:
a polynomial homogeneous of positive degree has no constant term, so every monomial in its
support involves some variable (`MvPolynomial.mem_ideal_span_X_image`). -/
theorem irrelevant_le_span_X :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    (HomogeneousIdeal.irrelevant
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  change p ∈ Ideal.span _
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hp' : p.IsWeightedHomogeneous (fun _ : σ => 1) i := hp
  have hwt := hp' (MvPolynomial.mem_support_iff.mp hm)
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun j => h j (Set.mem_univ j)
  subst hm0
  simp at hwt
  omega

/-- `D₊(x_i)` cover `Proj k[x]` (weights `1`). -/
theorem iSup_basicOpen_X_eq_top :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    ⨆ i : σ, AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (MvPolynomial.X i) = ⊤ := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _ (irrelevant_le_span_X k)

include hw in
/-- `U(ψ) = Proj k[x]`: `D₊(ψ x_i) = D₊(x_i^{w_i}) = D₊(x_i)` already cover. -/
theorem mapDomain_eq_top :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    AlgebraicGeometry.Proj.mapDomain (weightedPowerGradedHom k w) = ⊤ := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  apply top_le_iff.mp
  rw [← iSup_basicOpen_X_eq_top k]
  refine iSup_le fun i => ?_
  have h1 : AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (MvPolynomial.X i) =
      AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i)) := by
    rw [weightedPowerGradedHom_X, AlgebraicGeometry.Proj.basicOpen_pow _ _ _ (hw i)]
  rw [h1]
  exact le_iSup_of_le (MvPolynomial.X i) (le_iSup_of_le (w i) (le_iSup_of_le (hw i)
    (le_iSup_of_le (X_mem k w i) le_rfl)))

/-- The power map `P^{|σ|-1} = P(1,…,1) → P(w)`, `[u] ↦ [u^w]`: Stacks 01MY's `r_ψ` on
`U(ψ) = P^{|σ|-1}`. -/
def powerMap :
    weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ⟶ weightedProjectiveSpace k w hw :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  (AlgebraicGeometry.Scheme.topIso _).inv ≫
    (AlgebraicGeometry.Scheme.isoOfEq _ (mapDomain_eq_top k w hw).symm).hom ≫
    AlgebraicGeometry.Proj.mapOfGradedHom (weightedPowerGradedHom k w)

theorem inducedByPowerMap_powerMap : InducedByPowerMap (powerMap k w hw) :=
  ⟨mapDomain_eq_top k w hw, rfl⟩

/-- On the chart `D₊(x_i^{w_i}) ≅ Spec k[u]_(x_i^{w_i})` the power map is
`Spec (Away.map ψ x_i)` followed by `D₊(x_i) → P(w)` (Stacks 01MY, via `mapOfGradedHom_basicOpen`). -/
theorem awayι_comp_powerMap (i : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i))
        (psiX_mem k w i) (hw i) ≫ powerMap k w hw =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i)) ≫
        AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w)
          (MvPolynomial.X i) (X_mem k w i) (hw i) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  set ψ := weightedPowerGradedHom k w
  have hle : AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ (MvPolynomial.X i)) ≤
      AlgebraicGeometry.Proj.mapDomain ψ :=
    le_iSup_of_le (MvPolynomial.X i) (le_iSup_of_le (w i) (le_iSup_of_le (hw i)
      (le_iSup_of_le (X_mem k w i) le_rfl)))
  have key := AlgebraicGeometry.Proj.mapOfGradedHom_basicOpen ψ (MvPolynomial.X i) (w i) (hw i)
    (X_mem k w i)
  have hι : (AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) (ψ (MvPolynomial.X i))).ι ≫
        (AlgebraicGeometry.Scheme.topIso _).inv ≫
        (AlgebraicGeometry.Scheme.isoOfEq _ (mapDomain_eq_top k w hw).symm).hom =
      (AlgebraicGeometry.Proj
        (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).homOfLE hle := by
    rw [← cancel_mono (AlgebraicGeometry.Proj.mapDomain ψ).ι, AlgebraicGeometry.Scheme.homOfLE_ι,
      Category.assoc, Category.assoc, AlgebraicGeometry.Scheme.isoOfEq_hom_ι,
      AlgebraicGeometry.Scheme.toIso_inv_ι, Category.comp_id]
  refine Eq.trans ?_ key
  rw [← hι]
  unfold AlgebraicGeometry.Proj.awayι powerMap
  simp only [Category.assoc]
  rfl

include hw in
/-- Points of `Proj k[u]` (weights `1`) all lie on some chart `D₊(x_j^{w_j}) = D₊(x_j)`. -/
theorem exists_mem_basicOpen_pow :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    ∀ x : AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)),
    ∃ j : σ, x ∈ AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
      (weightedPowerGradedHom k w (MvPolynomial.X j)) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  intro x
  have hx : x ∈ (⊤ : (AlgebraicGeometry.Proj
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).Opens) := trivial
  rw [← iSup_basicOpen_X_eq_top k, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨j, hj⟩ := hx
  refine ⟨j, ?_⟩
  rwa [weightedPowerGradedHom_X, AlgebraicGeometry.Proj.basicOpen_pow _ _ _ (hw j)]

/-- `Away.map ψ x_j` sends the localization element `x_i^{w_j}/x_j^{w_i}` of `k[x]_(x_j)` to the
corresponding element `(x_i^{w_i})^{w_j}/(x_j^{w_j})^{w_i}` of `k[u]_(x_j^{w_j})`. -/
theorem awayMap_isLocalizationElem (i j : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    weightedPowerAwayMap k w hw j
        (HomogeneousLocalization.Away.isLocalizationElem (X_mem k w j) (X_mem k w i)) =
      HomogeneousLocalization.Away.isLocalizationElem
        (psiX_mem k w j) (psiX_mem k w i) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  unfold weightedPowerAwayMap HomogeneousLocalization.Away.isLocalizationElem
  rw [HomogeneousLocalization.Away.map_mk]
  congr 1
  exact map_pow _ _ _

/-- `powerMap⁻¹ D₊(x_i) = D₊(x_i^{w_i})`. -/
theorem powerMap_preimage_basicOpen (i : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    powerMap k w hw ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) =
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i)) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  change @Eq (AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))).Opens _ _
  apply le_antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_pow k w hw x
    obtain ⟨y, rfl⟩ : x ∈ (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ((weightedPowerGradedHom k w) (MvPolynomial.X j))
        (psiX_mem k w j) (hw j)).opensRange := by
      rwa [AlgebraicGeometry.Proj.opensRange_awayι]
    have h1 : powerMap k w hw (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ((weightedPowerGradedHom k w) (MvPolynomial.X j))
          (psiX_mem k w j) (hw j) y) =
        AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X j) (X_mem k w j) (hw j)
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw j)) y) :=
      (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ y).symm.trans
        ((congrArg (fun f => f y) (awayι_comp_powerMap k w hw j)).trans
          (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ y))
    have hx' : powerMap k w hw (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ((weightedPowerGradedHom k w) (MvPolynomial.X j))
          (psiX_mem k w j) (hw j) y) ∈
        AlgebraicGeometry.Proj.basicOpen (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) := hx
    rw [h1] at hx'
    have hy : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw j))) y ∈
        AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X j) (X_mem k w j) (hw j) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) := hx'
    rw [AlgebraicGeometry.Proj.awayι_preimage_basicOpen (MvPolynomial.weightedHomogeneousSubmodule k w) _ _ (X_mem k w i) (hw i)] at hy
    have hy' : y ∈ AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ((weightedPowerGradedHom k w) (MvPolynomial.X j))
        (psiX_mem k w j) (hw j) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ((weightedPowerGradedHom k w) (MvPolynomial.X i)) := by
      rw [AlgebraicGeometry.Proj.awayι_preimage_basicOpen (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) _ _ (psiX_mem k w i) (hw i),
        ← awayMap_isLocalizationElem k w hw i j]
      exact hy
    exact hy'
  · intro x hx
    obtain ⟨y, rfl⟩ : x ∈ (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) _ (psiX_mem k w i) (hw i)).opensRange := by
      rwa [AlgebraicGeometry.Proj.opensRange_awayι]
    have h1 : powerMap k w hw (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) ((weightedPowerGradedHom k w) (MvPolynomial.X i))
          (psiX_mem k w i) (hw i) y) =
        AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) (X_mem k w i) (hw i)
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i)) y) :=
      (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ y).symm.trans
        ((congrArg (fun f => f y) (awayι_comp_powerMap k w hw i)).trans
          (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ y))
    have h2 : AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) (X_mem k w i) (hw i)
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i)) y) ∈
        AlgebraicGeometry.Proj.basicOpen (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) :=
      (AlgebraicGeometry.Proj.opensRange_awayι (MvPolynomial.weightedHomogeneousSubmodule k w) _ (X_mem k w i) (hw i)).le ⟨_, rfl⟩
    rw [← h1] at h2
    exact h2

/-- The chart square of the power map is a pullback (both vertical arrows are the open immersions
`awayι`, and `D₊(x_i^{w_i})` is the preimage of `D₊(x_i)`). -/
theorem isPullback_awayι_powerMap (i : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    IsPullback (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (weightedPowerAwayMap k w hw i)))
      (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i))
        (psiX_mem k w i) (hw i))
      (AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w)
        (MvPolynomial.X i) (X_mem k w i) (hw i))
      (powerMap k w hw) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  refine AlgebraicGeometry.IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_powerMap k w hw i) ?_
  rw [AlgebraicGeometry.Proj.opensRange_awayι, AlgebraicGeometry.Proj.opensRange_awayι]
  exact powerMap_preimage_basicOpen k w hw i

end WeightedToOrdinaryProj

end
