import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGeneration
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseSubalgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGenerationMultipleCore

/-! # Veronese generation for positive multiples

The generation property of the Veronese algebra persists after replacing `m` by any positive
multiple `c · m`.

Source: Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem veronese_generation_multiple {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
    {σ : Type u} [Fintype σ] [Nonempty σ] {k : ℕ} (w : σ → ℕ) (hw : ∀ i, w i ∈ Finset.Icc 1 k)
    (hS : S.IsLocallyWeightedPolynomial w (fun i => (Finset.mem_Icc.mp (hw i)).1))
    (c : ℕ) (hc : 0 < c) :
    S.SufficientlyDivisible (c * (Fintype.card σ * jetWeight k)) := by
  refine ⟨Nat.mul_pos hc (veroneseDegree_pos k), ?_⟩
  apply veronese_generatedInDegreeOne_of_veronese S (Fintype.card σ * jetWeight k) c
  exact (veronese_generation S w hw hS).2

end
