import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjProperLocal

/-! # Weighted projective space is proper

The structure morphism of the weighted projective space `weightedProjectiveSpace k w hw` (finitely
many variables of positive weight) to `Spec k` is proper, registered as an **instance**; hence it is
also locally of finite type, quasi-compact, separated and universally closed (Mathlib derives these
from `IsProper`). The proof is `local_weightedProjToSpec_isProper`. References: Stacks 01NI, 0B5J.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry

/-- The structure morphism `P_k(w) → Spec k` is proper. -/
instance weightedProjectiveSpace_isProper (k : Type u) [Field k] {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    IsProper ((weightedProjectiveSpace k w hw) ↘ Spec (CommRingCat.of k)) :=
  MiyaokaMori.WeightedJets.local_weightedProjToSpec_isProper k (fun i => (⟨w i, hw i⟩ : ℕ+))

/-- The structure morphism `P_k(w) → Spec k` is locally of finite type. -/
instance weightedProjectiveSpace_locallyOfFiniteType (k : Type u) [Field k] {σ : Type u}
    [Finite σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    LocallyOfFiniteType ((weightedProjectiveSpace k w hw) ↘ Spec (CommRingCat.of k)) :=
  inferInstance
