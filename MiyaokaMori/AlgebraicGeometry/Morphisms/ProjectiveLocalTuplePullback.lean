import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLocalTuple
import MiyaokaMori.AlgebraicGeometry.Morphisms.PartialMapPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.PartialMapPullbackFunctionField

/-! # Pulling back a local tuple along a dominant `k`-morphism

If the rational map `g : X ⤏ P^N` is given at `f(x')` by the tuple `a`, then `g ∘ f` is given at `x'`
by `f^♯(a)` (cf. the proof of Debarre, *Introduction to Mori theory*, Thm 5.18, the sections
`s_i ∘ ε`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

theorem ProjectiveSpace.IsLocalTupleAt.pullbackAlong {k : Type u} [Field k] {N : ℕ}
    {X' X : Scheme.{u}} [IsIntegral X'] [IsIntegral X]
    [X'.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    (f : X' ⟶ X) [f.IsOver (Spec (CommRingCat.of k))] [IsDominant f]
    (g : X.PartialMap (ProjectiveSpace N k))
    (hd : Dense ((f ⁻¹ᵁ g.domain : X'.Opens) : Set X')) (x' : X')
    {a : Fin (N + 1) → X.presheaf.stalk (f x')}
    (h : ProjectiveSpace.IsLocalTupleAt k N g.fromFunctionField (f x') a) :
    ProjectiveSpace.IsLocalTupleAt k N (g.pullbackAlong f hd).fromFunctionField x'
      (fun i => (f.stalkMap x').hom (a i)) := by
  obtain ⟨hspan, hg⟩ := h
  obtain ⟨θ, hθ, hpull⟩ := Scheme.PartialMap.exists_functionField_hom_pullbackAlong f g hd
  have hsq : ∀ i, θ.hom (algebraMap (X.presheaf.stalk (f x')) X.functionField (a i)) =
      algebraMap (X'.presheaf.stalk x') X'.functionField ((f.stalkMap x').hom (a i)) := fun i =>
    congrArg (fun r => r (a i)) (hθ x')
  -- θ is compatible with the k-structures
  have hc : θ.hom.comp (X.stalkStructureHom k (genericPoint X)) =
      X'.stalkStructureHom k (genericPoint X') := by
    have h1 := X.stalkSpecializes_comp_stalkStructureHom k (genericPoint_specializes (f x'))
    have h2 := X'.stalkSpecializes_comp_stalkStructureHom k (genericPoint_specializes x')
    have h3 := Scheme.Hom.stalkMap_comp_stalkStructureHom k f x'
    have h1' : (algebraMap (X.presheaf.stalk (f x')) X.functionField).comp
        (X.stalkStructureHom k (f x')) = X.stalkStructureHom k (genericPoint X) := h1
    have h2' : (algebraMap (X'.presheaf.stalk x') X'.functionField).comp
        (X'.stalkStructureHom k x') = X'.stalkStructureHom k (genericPoint X') := h2
    rw [← h1', ← RingHom.comp_assoc, hθ x', RingHom.comp_assoc, h3, h2']
  have hspan1 : Ideal.span (Set.range fun i =>
      θ.hom (algebraMap (X.presheaf.stalk (f x')) X.functionField (a i))) = ⊤ := by
    have := congrArg (Ideal.map θ.hom) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  have hfun : (fun i => θ.hom (algebraMap (X.presheaf.stalk (f x')) X.functionField (a i))) =
      fun i => algebraMap (X'.presheaf.stalk x') X'.functionField ((f.stalkMap x').hom (a i)) :=
    funext hsq
  have hspan2 : Ideal.span (Set.range fun i =>
      algebraMap (X'.presheaf.stalk x') X'.functionField ((f.stalkMap x').hom (a i))) = ⊤ := by
    rw [← hfun]; exact hspan1
  refine ⟨hspan2, ?_⟩
  rw [hpull, hg]
  exact (ProjectiveSpace.tuplePoint_map k N (X.stalkStructureHom k (genericPoint X))
      (X'.stalkStructureHom k (genericPoint X')) θ.hom hc _ hspan hspan1).trans
    (ProjectiveSpace.tuplePoint_congr k N _ _ _ _ hspan1 hspan2 hfun)

end
