import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree

/-!
# Positivity of the degree of an effective zero cycle

The degree here is the existing residue-field-weighted degree of an actual
`DimensionCycle`.  Properness supplies finite support and, through its
`LocallyOfFiniteType` field, positive finite residue degrees at every point in
the support.  Thus a nonzero nonnegative coefficient gives a genuinely
positive integer summand.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

namespace AlgebraicGeometry.Intersection

universe u

/-- A nonzero zero cycle with nonnegative actual coefficients has positive raw degree. -/
theorem rawZeroCycleDegree_pos_of_nonneg
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (α : DimensionCycle X 0)
    (hα : ∀ x, 0 ≤ α.1 x)
    (hα_ne : ∃ x, α.1 x ≠ 0) :
    0 < rawZeroCycleDegree f α := by
  let s : Finset X := (properCycle_finiteSupport f α.1).toFinset
  have hs : ∀ x, x ∉ s → α.1 x = 0 := by
    intro x hx
    by_contra hne
    exact hx ((properCycle_finiteSupport f α.1).mem_toFinset.mpr hne)
  rw [rawZeroCycleDegree_eq_sum_on f α s hs]
  apply Finset.sum_pos'
  · intro x hx
    exact mul_nonneg (hα x) (Int.natCast_nonneg _)
  · rcases hα_ne with ⟨x, hx⟩
    have hxs : x ∈ s := (properCycle_finiteSupport f α.1).mem_toFinset.mpr hx
    have hcoeff : 0 < α.1 x := lt_of_le_of_ne (hα x) (Ne.symm hx)
    have hres : 0 < residueFieldDegree f x :=
      zeroCycle_residueFieldDegree_pos f α x hx
    have hres' : 0 < (residueFieldDegree f x : ℤ) := by
      exact_mod_cast hres
    exact ⟨x, hxs, mul_pos hcoeff hres'⟩

end AlgebraicGeometry.Intersection
