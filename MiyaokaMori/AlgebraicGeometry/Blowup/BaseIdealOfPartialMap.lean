import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLocalTupleExists
import MiyaokaMori.RingTheory.RegularLocalRing.PrimitiveTupleSpanPrimary
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.FinitePointsIdealSheaf

/-! # The base ideal of a partial map to projective space

For a `k`-partial map `g : X ⇢ P^N_k` and a finite set `T` of closed points whose local rings are
Noetherian UFDs of dimension `≤ 2`, there is an ideal sheaf `I` with support contained in `T` such that
at every `x ∈ T` the stalk is `I_x = (a_0, …, a_N)`, where `a` is a (primitive) local tuple of `g` at `x`.

Reference: Debarre, *Introduction to Mori theory*, proof of Theorem 5.18 (the common zeros of
`s_0, …, s_N` are the base points); Hartshorne II, Example 7.17.3 (the base ideal).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- Existence of the base ideal of a partial map `g : X ⇢ P^N_k` at a finite set `T` of closed points. -/
theorem ProjectiveSpace.exists_baseIdeal {k : Type u} [Field k] {N : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (g : X.PartialMap (ProjectiveSpace N k)) [g.IsOver (Spec (CommRingCat.of k))]
    (T : Set X) (hTfin : T.Finite) (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hTufd : ∀ x ∈ T, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (hTnoeth : ∀ x ∈ T, IsNoetherianRing (X.presheaf.stalk x))
    (hTdim : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) ≤ 2) :
    ∃ I : X.IdealSheafData, (I.support : Set X) ⊆ T ∧
      ∀ x ∈ T, ∃ a : Fin (N + 1) → X.presheaf.stalk x,
        ProjectiveSpace.IsLocalTupleAt k N g.fromFunctionField x a ∧
        I.stalkIdeal x = Ideal.span (Set.range a) := by
  classical
  have hex : ∀ x : X, x ∈ T → ∃ a : Fin (N + 1) → X.presheaf.stalk x,
      ProjectiveSpace.IsLocalTupleAt k N g.fromFunctionField x a ∧
      ∃ n : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ Ideal.span (Set.range a) := by
    intro x hx
    have := hTufd x hx
    have := hTnoeth x hx
    obtain ⟨a, hloc, hprim⟩ := ProjectiveSpace.exists_isLocalTupleAt_isPrimitiveTuple
      g.fromFunctionField g.fromFunctionField_comp_over x
    refine ⟨a, hloc, exists_maximalIdeal_pow_le_span_of_isPrimitiveTuple (hTdim x hx) a ?_ hprim⟩
    by_contra hne
    rw [not_exists] at hne
    obtain ⟨hspan, -⟩ := hloc
    have hbot : Ideal.span (Set.range fun i =>
        algebraMap (X.presheaf.stalk x) X.functionField (a i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      have : a i = 0 := by simpa using hne i
      simp [this]
    rw [hbot] at hspan
    exact bot_ne_top hspan
  choose a ha using hex
  let q : ∀ x : X, Ideal (X.presheaf.stalk x) := fun x =>
    if h : x ∈ T then Ideal.span (Set.range (a x h)) else ⊤
  have hq : ∀ x ∈ hTfin.toFinset, ∃ n : ℕ,
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ q x := by
    intro x hx
    have hxT : x ∈ T := hTfin.mem_toFinset.mp hx
    obtain ⟨n, hn⟩ := (ha x hxT).2
    exact ⟨n, by simpa [q, hxT] using hn⟩
  have hcl : ∀ x ∈ hTfin.toFinset, IsClosed ({x} : Set X) := fun x hx =>
    hTclosed x (hTfin.mem_toFinset.mp hx)
  refine ⟨X.finitePointsIdealSheaf hTfin.toFinset q, ?_, ?_⟩
  · have := X.finitePointsIdealSheaf_support_subset hTfin.toFinset q hcl hq
    simpa using this
  · intro x hx
    refine ⟨a x hx, (ha x hx).1, ?_⟩
    rw [X.finitePointsIdealSheaf_stalkIdeal hTfin.toFinset q hcl hq x (hTfin.mem_toFinset.mpr hx)]
    simp [q, hx]

end
