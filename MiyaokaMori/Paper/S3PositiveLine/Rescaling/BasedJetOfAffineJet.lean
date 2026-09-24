import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCoreWeightedRescaling_AffineJet
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetOfChartFamily

/-! # The parameter line and the based jet of an affine jet
(Lemma 3.1 of the paper, second paragraph of the proof
of Lemma 3.1)

Companion of `PositiveLineCoreWeightedRescaling_AffineJet`: the second half of the affine lift,
`weighted_rescaling_jet_of_affineJet`, assembled from `exists_basedJet_of_affineJet` (`BasedJetOfChartFamily`),
`HonestJetChart.fiberCoords_genericWeightedPoint` and `weightedPointOfCoords_scale`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- **The parameter line and the based jet of an affine jet** (Lemma 3.1 of the paper, second
paragraph of the proof of Lemma 3.1 of the paper). Input: the data produced
by `weighted_rescaling_generic_affineJet` — a finite cover `ρ : C̃ → C`, an affine jet
`ĵ : Spec κ(η_{C̃}) → J_κ^s` over `η_{C̃} ≫ ρ`, a family of affine honest charts `(V α, chart α)`
covering `C` and containing `η_C`, over all of which `ĵ` lies, its coordinate tuples `b α`
(`affineJetCoord`), not identically zero and with `(q+1)`-th roots in every chart, and a designated
chart `α₀` (the hypotheses of `exists_basedJet_of_affineJet`). Output: a line bundle `L` on `C̃`, a
based jet `J : C̃_(κ)(L) → 𝒵` over `ρ` with nowhere-zero normalized tuple and some nonzero
positive-order coefficient, whose generic weighted point has fiber coordinate
`weightedPointOfCoords (b α₀)` in the chart `α₀`.

Proof (every step names its lemma):
1. `exists_basedJet_of_affineJet` (`BasedJetOfChartFamily`; the paper's steps "weighted orders" — computed chart by chart,
   integral by the roots in every chart —, "`L = O(Σ w_y [y])`", "normalized coefficients", "local jets
   and gluing", Lemma 3.1 of the paper) gives `L`, `J`, `hnz`, a trivialization `e` of `η^*L^∨` on
   `Spec κ(η_{C̃})` and `γ ≠ 0` with `J.genericChartCoords … (chart α₀) … e (i,q) = γ^{q+1} b α₀ i q`.
2. `hne'` is `hnz` at the generic point (`NormalizedTupleNowhereZero.exists_coefficient_ne_zero`);
   `hx` is `BasedJet.genericWeightedPoint_range_subset`.
3. `HonestJetChart.fiberCoords_genericWeightedPoint` (Lemma 3.1 of the paper): the fiber coordinate of `J.genericWeightedPoint` in the chart `α₀` is the
   weighted point of the tuple of generic chart coordinates.
4. That tuple is `γ^{q+1} b α₀ i q`, a weighted rescaling of `b α₀`, so its weighted point is that of
   `b α₀` (`weightedPointOfCoords_scale`). ∎

Edge cases: `κ = 0` — `hne α` is impossible, vacuous; `n = 0` fine. -/
theorem weighted_rescaling_jet_of_affineJet [IsAlgClosed k]
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {ι : Type u} {V : ι → C.toScheme.Opens} (hV : ∀ α, AlgebraicGeometry.IsAffineOpen (V α))
    (chart : ∀ α, HonestJetChart f κ (V α)) (hηV : ∀ α, genericPoint C.toScheme ∈ V α)
    (hcover : ∀ c : C.toScheme, ∃ α, c ∈ V α)
    (hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α))
    (b : ι → Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hb : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      b α i q = affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i, q)))
    (hne : ∀ α, ∃ i q, b α i q ≠ 0)
    (hroot : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), b α i q ≠ 0 →
      ∃ c : ρ.source.toScheme.functionField, c ^ ((q : ℕ) + 1) = b α i q)
    (α₀ : ι) :
    ∃ (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
      (hnz : NormalizedTupleNowhereZero J)
      (hne' : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0)
      (hx : Set.range (J.genericWeightedPoint hne' ≫ YGG.proj f κ).base ⊆ V α₀),
      (chart α₀).fiberCoords (J.genericWeightedPoint hne') hx
        = weightedPointOfCoords ρ.source X.toVariety.dim κ (b α₀) (hne α₀) := by
  -- Step 1: the construction lemma
  obtain ⟨L, J, hnz, e, γ, hγ, hcoord⟩ :=
    exists_basedJet_of_affineJet f κ ρ ĵ hĵ hV chart hηV hcover hĵV b hb hne hroot α₀
  -- Step 2: `hne'` from `hnz`, `hx` from `hηV`
  have hne' : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0 := hnz.exists_coefficient_ne_zero
  set t : Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField :=
    fun i q => J.genericChartCoords hne' (chart α₀) (hηV α₀) e (i, q) with ht
  have hne_t : ∃ i q, t i q ≠ 0 := by
    obtain ⟨i, q, hiq⟩ := hne α₀
    refine ⟨i, q, ?_⟩
    rw [ht]
    show J.genericChartCoords hnz.exists_coefficient_ne_zero (chart α₀) (hηV α₀) e (i, q) ≠ 0
    rw [hcoord i q]
    exact mul_ne_zero (pow_ne_zero _ hγ) hiq
  refine ⟨L, J, hnz, hne', J.genericWeightedPoint_range_subset hne' (hηV α₀), ?_⟩
  -- Step 3: the fiber coordinate is the weighted point of the generic chart coordinates
  letI := ρ.source.functionFieldAlgebra
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have hB := (chart α₀).fiberCoords_genericWeightedPoint J hne' (hηV α₀) e
    ρ.source.SpecMap_algebraMap_functionFieldAlgebra (jetCoordTuple t hne_t) (fun p => rfl)
  -- Step 4: weighted rescaling by `γ` does not change the weighted point
  have hscale : weightedPointOfCoords ρ.source X.toVariety.dim κ t hne_t =
      weightedPointOfCoords ρ.source X.toVariety.dim κ (b α₀) (hne α₀) :=
    weightedPointOfCoords_scale ρ.source X.toVariety.dim κ (b α₀) t (hne α₀) hne_t γ hγ
      (fun i q => hcoord i q)
  exact hB.trans hscale

end
