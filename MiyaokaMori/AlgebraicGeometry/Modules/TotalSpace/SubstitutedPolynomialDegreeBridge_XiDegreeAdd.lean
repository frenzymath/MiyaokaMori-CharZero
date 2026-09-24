import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # Additivity of the ξ-degree

ξ-coefficients on `Tot(L)` are additive and vanish on `0`; hence the ξ-degree of a sum is at most the
maximum of the ξ-degrees, and the ξ-degree of a finite sum of sections of ξ-degree `≤ r` is `≤ r`.
(The ξ-expansion of `F_j(P_0,…,P_N)` is the sum of the expansions of its monomials; the coefficient map
`xiCoefficient` is a composite of `ModuleCat` homs, so additivity is `map_add` layer by layer.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `xiCoefficient` is additive: every layer of `totalSpace.coefficient` is a `ModuleCat` hom
(`map_add`); the `erw` crosses the type ascription `Γ(Tot, N) = Γ(C, p_*N)`. -/
theorem xiCoefficient_add {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    xiCoefficient L M (P + P') q = xiCoefficient L M P q + xiCoefficient L M P' q := by
  unfold xiCoefficient AlgebraicGeometry.Scheme.totalSpace.coefficient
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
  rw [map_add]
  erw [map_add]
  repeat' rw [map_add]

/-- `xiCoefficient 0 q = 0`. -/
theorem xiCoefficient_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q : ℕ) :
    xiCoefficient L M (0 : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) q = 0 := by
  unfold xiCoefficient AlgebraicGeometry.Scheme.totalSpace.coefficient
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
  rw [map_zero]
  erw [map_zero]
  repeat' rw [map_zero]

/-- `xiDegree 0 = ⊥`. -/
theorem xiDegree_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) :
    xiDegree L M (0 : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) = ⊥ := by
  unfold xiDegree
  rw [Finset.max_eq_bot]
  ext q
  simp [xiCoefficient_zero]

/-- `xiDegree (P + P') ≤ max (xiDegree P) (xiDegree P')`. -/
theorem xiDegree_add_le {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiDegree L M (P + P') ≤ max (xiDegree L M P) (xiDegree L M P') := by
  unfold xiDegree
  apply Finset.max_le
  intro a ha
  have hne : xiCoefficient L M (P + P') a ≠ 0 :=
    (xiCoefficient_finite_support L M (P + P')).mem_toFinset.mp ha
  rw [xiCoefficient_add] at hne
  by_cases h1 : xiCoefficient L M P a = 0
  · rw [h1, zero_add] at hne
    exact le_max_of_le_right (Finset.le_max ((xiCoefficient_finite_support L M P').mem_toFinset.mpr hne))
  · exact le_max_of_le_left (Finset.le_max ((xiCoefficient_finite_support L M P).mem_toFinset.mpr h1))

/-- A finite sum of sections of ξ-degree `≤ r` has ξ-degree `≤ r`. -/
theorem xiDegree_sum_le {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) {ι : Type*} (s : Finset ι)
    (f : ι → (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (r : WithBot ℕ)
    (hf : ∀ i ∈ s, xiDegree L M (f i) ≤ r) :
    xiDegree L M (∑ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [xiDegree_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (xiDegree_add_le L M _ _) (max_le (hf a (Finset.mem_insert_self a s)) ?_)
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

end
