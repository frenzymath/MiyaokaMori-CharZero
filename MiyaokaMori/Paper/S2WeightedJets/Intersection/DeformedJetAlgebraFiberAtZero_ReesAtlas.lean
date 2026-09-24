import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLocallyWeightedPolynomial

/-! # The weighted-polynomial atlas of the Rees deformation, as data

`reesDeformation_isLocallyWeightedPolynomial` (`DeformedJetAlgebraLocallyWeightedPolynomial`)
only *asserts* `Nonempty (atlas of R)`. The fibre chart of `T = s₀^*R` (`DeformedJetAlgebraFiberAtZero_FiberChart`,
used in `reesDeformation_restrictToLambda_zero_iso_weightedSym`) needs the atlas of `R := S.reesDeformation` as
**data** together with the characterisation of its chart isomorphisms, so the construction inside that proof is repeated
here as a `def`:

* `reesChartEquiv S 𝒜 hw i : R(V_i) ≃ₐ[Γ_i] Γ_i[y_s]` (`V_i := π⁻¹U_i = reesChart 𝒜 i`, `Γ_i := Γ(A¹_X, V_i)`) is
  `Φ_i⁻¹ ∘ Θ_i` for the two injective `Γ_i`-algebra maps `Θ_i := reesChartAlgHom` (`Ψ_i ∘ ι`) and
  `Φ_i := reesRescale λ_i w` (`y_s ↦ λ_i^{w s - 1} x_s`) with equal images (`AlgEquiv.ofInjective`, `Subalgebra.equivOfEq`);
* it is characterised by `reesRescale_reesChartEquiv : Φ_i (e_i a) = Θ_i a`;
* `reesAtlas S 𝒜 hw : R.toGradedAffineAlgebra.WeightedPolynomialAtlas w` with `chart i = reesChart 𝒜 i` and
  `equiv i = (reesChartEquiv S 𝒜 hw i).toRingEquiv` (both `rfl`).

The inputs are `reesChartAlgHom_injective`, `reesRescale_injective` (with `lambdaRes_mem_nonZeroDivisors`),
`map_pullbackAtlasPieceLin_range_incl` and `range_reesRescale_toLinearMap`.

Source: Lemma 2.3 of the paper ("removing the nonlinear terms"); Stacks 052P.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
variable {σ : Type u} {w : σ → ℕ} (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (hw : ∀ s, 0 < w s) (i : 𝒜.I)

/-- `Φ_i := reesRescale λ_i w` is injective (`λ_i` is a nonzerodivisor on the affine chart `V_i`). -/
theorem reesRescale_lambdaRes_reesChart_injective :
    Function.Injective
      (MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w) :=
  MvPolynomial.reesRescale_injective _
    (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes_mem_nonZeroDivisors (𝒜.chart i).2) w

include hw in
/-- **(B) The image of `Θ_i = Ψ_i ∘ ι : R(V_i) → Γ_i[x_s]` is `⊕_j reesSpan λ_i w j`.** -/
theorem reesChartAlgHom_range_eq :
    LinearMap.range (S.reesChartAlgHom 𝒜 i).toLinearMap =
      ⨆ j, MvPolynomial.reesSpan (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w j := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [AlgHom.toLinearMap_apply]
    suffices h : ∀ y : DirectSum ℕ (S.reesDeformation.sectionsPiece (S.reesChart 𝒜 i).toOpens),
        S.reesChartAlgHom 𝒜 i y ∈ ⨆ j, MvPolynomial.reesSpan
          (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w j from h x
    intro y
    induction y using DirectSum.induction_on with
    | zero =>
      have h0 : S.reesChartAlgHom 𝒜 i (0 : DirectSum ℕ (S.reesDeformation.sectionsPiece (S.reesChart 𝒜 i).toOpens)) = 0 :=
        map_zero _
      rw [h0]; exact zero_mem _
    | of m a =>
      refine Submodule.mem_iSup_of_mem m ?_
      rw [← S.map_pullbackAtlasPieceLin_range_incl 𝒜 i hw m]
      exact Submodule.mem_map.2 ⟨(AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.incl S m).app _ a,
        LinearMap.mem_range.2 ⟨a, rfl⟩, (S.reesChartAlgHom_ofPiece 𝒜 i m a).symm⟩
    | add x y hx hy =>
      have hadd : S.reesChartAlgHom 𝒜 i (x + y) = S.reesChartAlgHom 𝒜 i x + S.reesChartAlgHom 𝒜 i y :=
        map_add _ x y
      rw [hadd]; exact add_mem hx hy
  · refine iSup_le fun j => ?_
    rw [← S.map_pullbackAtlasPieceLin_range_incl 𝒜 i hw j]
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨S.reesDeformation.ofPiece _ j y, S.reesChartAlgHom_ofPiece 𝒜 i j y⟩

include hw in
/-- `Θ_i` and `Φ_i` have the same image (`(B)` and (a6.v) `range_reesRescale_toLinearMap`). -/
theorem reesChartAlgHom_range_eq_reesRescale_range :
    (S.reesChartAlgHom 𝒜 i).range =
      (MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w).range := by
  ext q
  rw [AlgHom.mem_range, AlgHom.mem_range]
  have h1 : q ∈ LinearMap.range (S.reesChartAlgHom 𝒜 i).toLinearMap ↔ q ∈ LinearMap.range
      (MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w).toLinearMap := by
    rw [S.reesChartAlgHom_range_eq 𝒜 hw i, MvPolynomial.range_reesRescale_toLinearMap _ w hw]
  simpa only [LinearMap.mem_range, AlgHom.toLinearMap_apply] using h1

include hw in
/-- **The chart isomorphism of the Rees deformation** `e_i := Φ_i⁻¹ ∘ Θ_i : R(V_i) ≃ₐ[Γ_i] Γ_i[y_s]`. -/
def reesChartEquiv :
    S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i)
      ≃ₐ[Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens)]
        MvPolynomial σ Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) :=
  (AlgEquiv.ofInjective _ (S.reesChartAlgHom_injective 𝒜 i)).trans
    ((Subalgebra.equivOfEq _ _ (S.reesChartAlgHom_range_eq_reesRescale_range 𝒜 hw i)).trans
      (AlgEquiv.ofInjective _ (S.reesRescale_lambdaRes_reesChart_injective 𝒜 i)).symm)

/-- **Characterisation of `e_i`**: `Φ_i (e_i a) = Θ_i a`, i.e. `reesRescale λ_i w (e_i a) = Ψ_i (ι a)`. -/
theorem reesRescale_reesChartEquiv
    (a : S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i)) :
    MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w
        (S.reesChartEquiv 𝒜 hw i a) = S.reesChartAlgHom 𝒜 i a :=
  congrArg Subtype.val (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjective _ (S.reesRescale_lambdaRes_reesChart_injective 𝒜 i))
    (Subalgebra.equivOfEq _ _ (S.reesChartAlgHom_range_eq_reesRescale_range 𝒜 hw i)
      (AlgEquiv.ofInjective _ (S.reesChartAlgHom_injective 𝒜 i) a)))

/-- `e_i` matches the gradings: `a ∈ R_m(V_i) ↔ e_i a` is weighted-homogeneous of weight `m`. -/
theorem reesChartEquiv_mem_grading_iff (m : ℕ)
    (a : S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i)) :
    a ∈ S.reesDeformation.toGradedAffineAlgebra.grading (S.reesChart 𝒜 i) m ↔
      (S.reesChartEquiv 𝒜 hw i a).IsWeightedHomogeneous w m := by
  have h1 := GradedRingHom.mem_iff_of_injective
    ((AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation.inclHom S).sectionsGradedRingHom (S.reesChart 𝒜 i).toOpens)
    (S.reesInclRingHom_injective 𝒜 i) m a
  have h2 := S.pullbackAtlasEquiv_grading (AlgebraicGeometry.Scheme.affineLineOver.toBase X) 𝒜 i (S.reesChart 𝒜 i) le_rfl
    (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
      (S.reesChart 𝒜 i) le_rfl) m (S.reesInclRingHom 𝒜 i a)
  let ΦG : MvPolynomial.weightedHomogeneousSubmodule Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) w
      →+*ᵍ MvPolynomial.weightedHomogeneousSubmodule Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens) w :=
    { toRingHom := (MvPolynomial.reesRescale
        (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w).toRingHom
      map_mem := fun {m} {p} hp => MvPolynomial.reesRescale_isWeightedHomogeneous _ w hp }
  have h3 := GradedRingHom.mem_iff_of_injective ΦG (S.reesRescale_lambdaRes_reesChart_injective 𝒜 i) m
    (S.reesChartEquiv 𝒜 hw i a)
  have h4 : MvPolynomial.reesRescale (AlgebraicGeometry.Scheme.affineLineOver.lambdaRes (S.reesChart 𝒜 i).toOpens) w
      (S.reesChartEquiv 𝒜 hw i a) = S.pullbackAtlasEquiv (AlgebraicGeometry.Scheme.affineLineOver.toBase X) 𝒜 i
        (S.reesChart 𝒜 i) le_rfl
        (S.pullbackTensorAlgHom_bijective (AlgebraicGeometry.Scheme.affineLineOver.toBase X) (𝒜.chart i)
          (S.reesChart 𝒜 i) le_rfl) (S.reesInclRingHom 𝒜 i a) := S.reesRescale_reesChartEquiv 𝒜 hw i a
  refine h1.trans (h2.trans ?_)
  rw [← h4]
  exact h3.symm

/-- `e_i` sends the structure map to the constants. -/
theorem reesChartEquiv_unitHom (r : Γ(AlgebraicGeometry.Scheme.affineLineOver X, (S.reesChart 𝒜 i).toOpens)) :
    S.reesChartEquiv 𝒜 hw i (S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.unitHom (S.reesChart 𝒜 i) r) =
      MvPolynomial.C r := by
  apply S.reesRescale_lambdaRes_reesChart_injective 𝒜 i
  rw [S.reesRescale_reesChartEquiv 𝒜 hw i, MvPolynomial.reesRescale_C]
  exact (S.reesChartAlgHom 𝒜 i).commutes r

include hw in
/-- **The weighted-polynomial atlas of the Rees deformation, as data**: charts `V_i = π⁻¹U_i`, chart isomorphisms
`reesChartEquiv`. -/
def reesAtlas : S.reesDeformation.toGradedAffineAlgebra.WeightedPolynomialAtlas w where
  I := 𝒜.I
  chart i := S.reesChart 𝒜 i
  covers v := by
    obtain ⟨i, hi⟩ := 𝒜.covers ((AlgebraicGeometry.Scheme.affineLineOver.toBase X).base v)
    exact ⟨i, hi⟩
  equiv i := (S.reesChartEquiv 𝒜 hw i).toRingEquiv
  equiv_grading i m a := S.reesChartEquiv_mem_grading_iff 𝒜 hw i m a
  equiv_unit i r := S.reesChartEquiv_unitHom 𝒜 hw i r

theorem reesAtlas_chart : (S.reesAtlas 𝒜 hw).chart i = S.reesChart 𝒜 i := rfl

theorem reesAtlas_equiv_apply (a : S.reesDeformation.toGradedAffineAlgebra.toAffineAlgebra.sections (S.reesChart 𝒜 i)) :
    (S.reesAtlas 𝒜 hw).equiv i a = S.reesChartEquiv 𝒜 hw i a := rfl

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
