import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.RingTheory.RegularLocalRing.PrimitiveTuple
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLocalTupleMemDomain
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveLocalTuplePullback
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealComap
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartierStalkPrincipal

/-! # Extension of a rational map after making the base ideal invertible

Let `f : X' → X` be dominant and `g : X ⇢ P^N_k` a partial map defined outside a set `T`, given at every
point of `T` by a tuple generating the stalk `I_x` of an ideal sheaf `I`. If `f⁻¹I·O_{X'}` is the ideal
sheaf of an effective Cartier divisor, then `g ∘ f` is defined on all of `X'`.

Reference: Hartshorne II, Example 7.17.3 (after blowing up the base ideal the `sᵢ` generate an invertible
sheaf, which gives the extended morphism); Debarre, *Introduction to Mori theory*, end of the proof of
Theorem 5.18.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- If the pullback `I.comap f` of the base ideal is the ideal sheaf of an effective Cartier divisor, the
rational map `g ∘ f` to `P^N_k` is everywhere defined. -/
theorem ProjectiveSpace.pullbackAlong_domain_eq_top_of_comap_baseIdeal {k : Type u} [Field k] {N : ℕ}
    {X' X : Scheme.{u}} [IsIntegral X'] [IsIntegral X]
    [X'.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (ProjectiveSpace N k ↘ Spec (CommRingCat.of k))]
    (f : X' ⟶ X) [f.IsOver (Spec (CommRingCat.of k))] [IsDominant f]
    (g : X.PartialMap (ProjectiveSpace N k))
    (hd : Dense ((f ⁻¹ᵁ g.domain : X'.Opens) : Set X'))
    (T : Set X) (hT : ∀ x, x ∉ T → x ∈ g.domain)
    (I : X.IdealSheafData)
    (hI : ∀ x ∈ T, ∃ a : Fin (N + 1) → X.presheaf.stalk x,
      ProjectiveSpace.IsLocalTupleAt k N g.fromFunctionField x a ∧
      I.stalkIdeal x = Ideal.span (Set.range a))
    (D : EffectiveCartierDivisor X') (hD : D.idealSheaf = I.comap f) :
    (g.pullbackAlong f hd).toRationalMap.domain = ⊤ := by
  rw [eq_top_iff]
  intro x' _
  by_cases hx : f x' ∈ T
  · obtain ⟨a, hloc, hIa⟩ := hI (f x') hx
    obtain ⟨d, hd0, hDd⟩ := D.exists_stalkIdeal_eq_span_singleton x'
    have hspan : Ideal.span (Set.range fun i => (f.stalkMap x').hom (a i)) = Ideal.span {d} := by
      rw [← hDd, hD, Scheme.IdealSheafData.stalkIdeal_comap, hIa, Ideal.map_span, ← Set.range_comp]
      rfl
    obtain ⟨e, hbe, j, hj⟩ := exists_unit_cofactor_of_span_range_eq_span_singleton
      (fun i => (f.stalkMap x').hom (a i)) d
      (fun r hr => (mul_eq_zero.mp hr).resolve_left hd0) hspan
    have hloc' := (ProjectiveSpace.IsLocalTupleAt.pullbackAlong f g hd x' hloc).of_mul d hd0 e hbe
    exact ProjectiveSpace.IsLocalTupleAt.mem_domain (g.pullbackAlong f hd).toRationalMap hloc' j hj
  · exact (g.pullbackAlong f hd).le_domain_toRationalMap (hT (f x') hx)

end
