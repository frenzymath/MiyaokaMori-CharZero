import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseClosedPoint
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty

/-! # The constant term of a jet

The constant term: the closed immersion `W ⟶ W × Spec k[t]/(t^{k+1})` induced by `t ↦ 0`; restriction along it takes
the constant term of a jet (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `t ↦ 0` is a section of the structure morphism `D_r ⟶ Spec k`: `ε ∘ (k → k[t]/(t^{r+1})) = id`
(`epsilon_eta`). -/

theorem jetBaseZero_comp_structure (k : Type u) [Field k] (r : ℕ) :
    jetBaseZero k r ≫ (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.CategoryStruct.id _ := by
  show AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ = _
  rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := k) r).comp
      (algebraMap k (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r)) = RingHom.id k :=
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_eta r
  rw [h]
  simp

/-- The `pullback.lift` compatibility condition for `jetConstantTerm`:
`𝟙 ≫ (W → Spec k) = ((W → Spec k) ≫ jetBaseZero) ≫ (D_r → Spec k)`. -/

theorem jetConstantTerm_cond {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    CategoryTheory.CategoryStruct.id W ≫ (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ jetBaseZero k r) ≫
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  rw [CategoryTheory.Category.id_comp, CategoryTheory.Category.assoc,
    jetBaseZero_comp_structure, CategoryTheory.Category.comp_id]

noncomputable def jetConstantTerm {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : W ⟶ jetThickening (k := k) r W :=
  CategoryTheory.Limits.pullback.lift (CategoryTheory.CategoryStruct.id W)
    ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ jetBaseZero k r)
    (jetConstantTerm_cond (k := k) r W)

end
