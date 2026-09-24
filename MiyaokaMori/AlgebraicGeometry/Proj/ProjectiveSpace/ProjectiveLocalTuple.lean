import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTuplePoint
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.StalkStructureHom

/-! # Local tuples of a function-field point of projective space

For an integral `k`-scheme `X`, the predicate that the function-field point
`ψ_K : Spec K(X) → P^N_k` is given at a point `x` by a tuple `a ∈ O_{X,x}^{N+1}` on the stalk
(`ψ_K = [a₀ : … : a_N]`), and its invariance under removing a common factor.

Source: Debarre, *Introduction to Mori theory*, proof of Theorem 5.18
(`π(x) = (s₀(x), …, s_N(x))`, `s_i ∘ ε = s̃_i · s_E^m`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- `ψ_K = [a₀ : … : a_N]`, where the `a_i ∈ O_{X,x}` are regarded as elements of `K(X)`; they are
required not to vanish simultaneously, i.e. to generate the unit ideal of the field `K(X)`. -/
def ProjectiveSpace.IsLocalTupleAt (k : Type u) [Field k] (N : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))] (ψK : Spec X.functionField ⟶ ProjectiveSpace N k) (x : X)
    (a : Fin (N + 1) → X.presheaf.stalk x) : Prop :=
  ∃ h : Ideal.span (Set.range fun i => algebraMap (X.presheaf.stalk x) X.functionField (a i)) = ⊤,
    ψK = ProjectiveSpace.tuplePoint k N X.functionField (X.stalkStructureHom k (genericPoint X))
      (fun i => algebraMap (X.presheaf.stalk x) X.functionField (a i)) h

/-- Removing a common factor: if `a_i = d · e_i` with `d ≠ 0`, then `e` is also a tuple of `ψ_K` at `x`. -/
theorem ProjectiveSpace.IsLocalTupleAt.of_mul {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    {ψK : Spec X.functionField ⟶ ProjectiveSpace N k} {x : X}
    {a : Fin (N + 1) → X.presheaf.stalk x} (h : ProjectiveSpace.IsLocalTupleAt k N ψK x a)
    (d : X.presheaf.stalk x) (hd : d ≠ 0) (e : Fin (N + 1) → X.presheaf.stalk x)
    (hae : ∀ i, a i = d * e i) : ProjectiveSpace.IsLocalTupleAt k N ψK x e := by
  obtain ⟨hspan, hψ⟩ := h
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hd' : algebraMap (X.presheaf.stalk x) X.functionField d ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hd
  let u : (X.functionField)ˣ := Units.mk0 _ hd'
  have hfun : (fun i => algebraMap (X.presheaf.stalk x) X.functionField (a i)) =
      fun i => (u : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField (e i) := by
    funext i
    rw [hae i, map_mul]
    rfl
  have hspan_e : Ideal.span (Set.range fun i =>
      algebraMap (X.presheaf.stalk x) X.functionField (e i)) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    show algebraMap (X.presheaf.stalk x) X.functionField (a i) ∈ _
    rw [hae i, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hspan' : Ideal.span (Set.range fun i =>
      (u : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField (e i)) = ⊤ := by
    rw [← hfun]; exact hspan
  refine ⟨hspan_e, hψ.trans ?_⟩
  exact (ProjectiveSpace.tuplePoint_congr k N _ _ _ _ hspan hspan' hfun).trans
    (ProjectiveSpace.tuplePoint_smul_unit k N _ u _ hspan_e hspan')

end
