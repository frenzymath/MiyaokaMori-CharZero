import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf

/-! # Weighted projective space

The weighted projective space `P_k(w) = Proj k[x_σ]` (`deg x_i = w_i`) obtained by instantiating
`Proj` with Mathlib's weighted grading on `MvPolynomial`, together with its structure as a
`k`-scheme and its twisting sheaves `O(m)`. The paper uses the weighted projective space with
`n + 1` coordinates in each of the weights `1, …, k` (see the Veronese polarization lemma).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The weighted projective space `P_k(w) = Proj k[x_σ]` (`deg x_i = w_i`), i.e. `weightedProj` with
the weights `w` and their positivity `hw` packaged as `ℕ+` (the grading `weightedPolynomialGrading`
is `weightedHomogeneousSubmodule k w`).

This is an `abbrev`, not a `def`, so that every `weightedProj`-level lemma
(`weightedCoordinateOpen`, `weightedCoordinateChartIso`, `ProjTwisting.*`, …) applies to
`weightedProjectiveSpace k w hw` without `unfold`. -/

noncomputable abbrev weightedProjectiveSpace (k : Type u) [Field k] {σ : Type u} (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) : AlgebraicGeometry.Scheme.{u} :=
  MiyaokaMori.WeightedJets.weightedProj k (fun i => (⟨w i, hw i⟩ : ℕ+))

/-- The structure morphism `P_k(w) → Spec k`: `weightedProjToSpec`, i.e. `Proj.toSpecZero` followed
by `Spec` of `k → k[x]_0`. -/

noncomputable instance (k : Type u) [Field k] {σ : Type u} (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    (weightedProjectiveSpace k w hw).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨MiyaokaMori.WeightedJets.weightedProjToSpec k (fun i => (⟨w i, hw i⟩ : ℕ+))⟩

/-- The twisting sheaf `O(m)` on `P_k(w)`: `weightedProjTwisting` (`= ProjTwisting.sheaf`, the same
object as `Proj.twist`). -/

noncomputable abbrev weightedProjTwist (k : Type u) [Field k] {σ : Type u} (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (m : ℤ) : (weightedProjectiveSpace k w hw).Modules :=
  MiyaokaMori.WeightedJets.weightedProjTwisting k (fun i => (⟨w i, hw i⟩ : ℕ+)) m

end
