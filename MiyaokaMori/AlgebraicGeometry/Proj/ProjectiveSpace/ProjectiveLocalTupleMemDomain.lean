import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLocalTuple
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTuplePointOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.RationalMapMemDomainOfStalk

/-! # A rational map to projective space is defined where a local tuple has a unit entry

If a rational map `ψ : X ⤏ P^N_k` is given at `x` by a tuple `a` and some `a_j` is a unit of
`O_{X,x}`, then `ψ` is defined at `x`.

Source: Hartshorne II, Theorem 7.1(b) and Example 7.17.3; Debarre, *Introduction to Mori theory*,
last paragraph of the proof of Theorem 5.18 (the `s̃_i` do not all vanish, so `π̃` is
defined).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

theorem ProjectiveSpace.IsLocalTupleAt.mem_domain {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (ProjectiveSpace N k ↘ Spec (CommRingCat.of k))]
    (ψ : X ⤏ ProjectiveSpace N k) {x : X} {a : Fin (N + 1) → X.presheaf.stalk x}
    (h : ProjectiveSpace.IsLocalTupleAt k N ψ.fromFunctionField x a) (j : Fin (N + 1))
    (hj : IsUnit (a j)) : x ∈ ψ.domain := by
  obtain ⟨hspan, hψ⟩ := h
  have hb : Ideal.span (Set.range a) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) hj
  refine AlgebraicGeometry.Scheme.RationalMap.mem_domain_of_fromSpecStalk
    (S := Spec (CommRingCat.of k)) ψ x
    (ProjectiveSpace.tuplePoint k N (X.presheaf.stalk x) (X.stalkStructureHom k x) a hb) ?_ ?_
  · rw [ProjectiveSpace.tuplePoint_over, X.SpecMap_stalkStructureHom k x]
  · rw [hψ]
    exact ProjectiveSpace.tuplePoint_map k N (X.stalkStructureHom k x)
      (X.stalkStructureHom k (genericPoint X))
      (algebraMap (X.presheaf.stalk x) X.functionField)
      (X.stalkSpecializes_comp_stalkStructureHom k _) a hb hspan

end
