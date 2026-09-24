import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.BasedJetGenericChartCoords

/-! # The defining equation of `BasedJet.genericChartCoords`, as a rewrite lemma

`BasedJet.genericChartCoords hne chart hηV e p` is *by definition*
`ι_K⁻¹ (ΓSpecIso (liftLocalPieceAux (J.genericLiftData hne) (𝟙 _) e V _ (w p) (x_p)))`. This module states
that `rfl` as a lemma, so that users can `rw` with it instead of unfolding the definition.

**Why a separate module.** The bare `rfl` is slow *in the kernel*: the body of the
`def` stores the `QuasiSober` / `IrreducibleSpace` instance arguments of `genericPoint ρ.source.toScheme` as
auto-generated auxiliary proofs (`BasedJet.genericChartCoords._proof_3/_proof_4`, produced by the nested-proof
abstraction of definitions), whereas every term written in a theorem statement carries the explicit instance
terms (`instQuasiSober…`, `irreducibleSpace_of_isIntegral _ _`). `Spec κ(η)` occurs in hundreds of implicit
arguments, so comparing the unfolded definition with any hand-written term costs one proof-irrelevance check per
occurrence (`rw`/`show`/`congrArg` all pay it). Isolating the comparison here keeps the main theorem fast:
after `rw [genericChartCoords_eq_liftLocalPieceAux]` all terms are in the "statement" representation.
Since `genericChartCoords` has the layered body `ρ.genericBaseToFunctionField (J.genericChartCoordsAux …)`,
the proof unfolds layer by layer (`genericChartCoords`, `genericChartCoordsAux_eq`, `liftLocalPieceAuxApply_eq`,
then `rfl` for `genericBaseToFunctionField`), which is much cheaper than a bare `rfl`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- The defining equation of `BasedJet.genericChartCoords` (definitional; see the module docstring for why it is
stated separately and how it is proved). -/
theorem BasedJet.genericChartCoords_eq_liftLocalPieceAux {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) {V : C.toScheme.Opens}
    (chart : HonestJetChart f κ V) (hηV : genericPoint C.toScheme ∈ V)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback
          (𝟙 (AlgebraicGeometry.Spec
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme))).obj
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≅
        SheafOfModules.unit (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).ringCatSheaf)
    (p : Fin (X.toVariety.dim + 1) × Fin κ) :
    J.genericChartCoords hne chart hηV e p =
      (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
      ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
            (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).hom.hom
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux (J.genericLiftData hne) (𝟙 _) e V
            (ρ.top_le_genericBase_preimage hηV) (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) (chart.coords p)))) := by
  rw [BasedJet.genericChartCoords, BasedJet.genericChartCoordsAux_eq,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAuxApply_eq]
  rfl

end
