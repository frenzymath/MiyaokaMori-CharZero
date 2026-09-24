import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLocalTuple
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveFieldPointIsTuple
import MiyaokaMori.RingTheory.PrimitiveTupleOfFractions

/-! # Existence of a primitive local tuple

At a point whose stalk is a UFD, the function-field point `ψ_K : Spec K(X) → P^N_k` is always given
by a primitive tuple (clear denominators and remove the common factor; this is the removal of the
fixed divisorial components of the linear system).

Source: Debarre, *Introduction to Mori theory*, first paragraph of the proof of
Theorem 5.18; Corollary 4.3 of the paper ("after removing fixed divisorial
components").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- The function-field point of a partial map over `k` is a `k`-morphism. -/
theorem AlgebraicGeometry.Scheme.PartialMap.fromFunctionField_comp_over {X Y S : Scheme.{u}}
    [X.Over S] [Y.Over S] [IrreducibleSpace X] (g : X.PartialMap Y) [g.IsOver S] :
    g.fromFunctionField ≫ (Y ↘ S) = X.fromSpecStalk (genericPoint X) ≫ (X ↘ S) := by
  have h : g.hom ≫ (Y ↘ S) = g.domain.ι ≫ (X ↘ S) := Scheme.PartialMap.isOver_iff.mp inferInstance
  simp only [Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc, h]
  rw [Scheme.Opens.fromSpecStalkOfMem_ι_assoc]

theorem ProjectiveSpace.exists_isLocalTupleAt_isPrimitiveTuple {k : Type u} [Field k] {N : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (ψK : Spec X.functionField ⟶ ProjectiveSpace N k)
    (hψK : ψK ≫ (ProjectiveSpace N k ↘ Spec (CommRingCat.of k)) =
      X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (CommRingCat.of k)))
    (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ a : Fin (N + 1) → X.presheaf.stalk x,
      ProjectiveSpace.IsLocalTupleAt k N ψK x a ∧ IsPrimitiveTuple a := by
  have hx : ψK ≫ (ProjectiveSpace N k ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (X.stalkStructureHom k (genericPoint X))) := by
    rw [hψK, X.SpecMap_stalkStructureHom k (genericPoint X)]
  obtain ⟨f, hf, hψ⟩ := ProjectiveSpace.exists_tuplePoint_of_field k N X.functionField
    (X.stalkStructureHom k (genericPoint X)) ψK hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    have hbot : Ideal.span (Set.range (0 : Fin (N + 1) → X.functionField)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      rfl
    rw [hbot] at hf
    exact bot_ne_top hf
  obtain ⟨c, a, hfa, hprim⟩ := exists_primitive_tuple_of_fractions
    (A := X.presheaf.stalk x) (K := X.functionField) f hf0
  have hfun : f = fun i => (c : X.functionField) *
      algebraMap (X.presheaf.stalk x) X.functionField (a i) := funext hfa
  have hspan' : Ideal.span (Set.range fun i => (c : X.functionField) *
      algebraMap (X.presheaf.stalk x) X.functionField (a i)) = ⊤ := by
    rw [← hfun]; exact hf
  have hspan : Ideal.span (Set.range fun i =>
      algebraMap (X.presheaf.stalk x) X.functionField (a i)) = ⊤ := by
    rw [eq_top_iff, ← hspan']
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨a, ⟨hspan, hψ.trans ?_⟩, hprim⟩
  exact (ProjectiveSpace.tuplePoint_congr k N _ _ _ _ hf hspan' hfun).trans
    (ProjectiveSpace.tuplePoint_smul_unit k N _ c _ hspan hspan')

end
