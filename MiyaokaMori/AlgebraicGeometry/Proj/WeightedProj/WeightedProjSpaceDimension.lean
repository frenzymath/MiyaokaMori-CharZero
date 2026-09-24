import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceDimension
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedToOrdinaryProj
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0ecg

/-! # Dimension of weighted projective space

The weighted projective space `P(a_0, …, a_N)` has dimension `N` (the fiber dimension `(n+1)k − 1`
in the Veronese polarization lemma of the paper). Proof: the power map `P^N → P(w)` is finite and
surjective, and finite surjective morphisms preserve the topological Krull dimension.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `dim P_k(w) = |σ| − 1` for a nonempty finite set `σ` of coordinates. -/
theorem weightedProjectiveSpace_dimension (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    topologicalKrullDim (weightedProjectiveSpace k w hw) = ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨g, hfinite, hsurjective, -⟩ := finite_surjective_toWeightedProj k w hw
  let hfinite' : AlgebraicGeometry.IsFinite g := hfinite
  let hsurjective' : AlgebraicGeometry.Surjective g := ⟨hsurjective⟩
  rw [← AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective g]
  exact weightedProjectiveSpace_one_dimension k

end
