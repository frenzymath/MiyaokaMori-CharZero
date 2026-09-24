import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.NormalizedTupleNowhereZero
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjSeparated

/-! # The morphism `τ`

The normalized tuple is nowhere simultaneously zero, so it defines `τ : C̃ → Y_k^GG`; `τ` agrees with `ν₀ ∘ η`
at the generic point, hence everywhere by separatedness (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem exists_tau {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) {Ct₀ : SmoothProjectiveCurve k}
    (ν₀ : Ct₀.toScheme ⟶ YGG f κ) (ρ : FiniteCover k C)
    (η : ρ.source.toScheme ⟶ Ct₀.toScheme) (L : LineBundle ρ.source.toVariety)
    (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0)
    (hgen : J.genericWeightedPoint hne
      = ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ η ≫ ν₀) :
    ∃ τ : ρ.source.toScheme ⟶ YGG f κ,
      τ = J.projectivize hnz ∧ τ ≫ YGG.proj f κ = ρ.hom ∧ τ = η ≫ ν₀ := by
  refine ⟨J.projectivize hnz, rfl, J.projectivize_proj hnz, ?_⟩
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  -- Y_k^GG is separated: π_k is separated (a relative Proj) and C → Spec k is separated
  have hπ : AlgebraicGeometry.IsSeparated (YGG.proj f κ) :=
    AlgebraicGeometry.Scheme.relativeProj_isSeparated _
  have hC : AlgebraicGeometry.IsSeparated
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := C.isSeparated
  have hY : (YGG f κ).IsSeparated := by
    refine ⟨?_⟩
    rw [← terminal.comp_from
      (YGG.proj f κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))]
    infer_instance
  -- the generic point is dense, and the two morphisms agree there
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq _ _ (terminal.from _)
    {genericPoint ρ.source.toScheme} ?_ ?_ (terminal.hom_ext _ _)
  · exact dense_iff_closure_eq.mpr (genericPoint_spec ρ.source.toScheme).def
  · rintro x rfl
    rw [← J.genericWeightedPoint_eq hnz hne, hgen]

end
