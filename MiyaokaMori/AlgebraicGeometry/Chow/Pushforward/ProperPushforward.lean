import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AlgebraicCycles
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper pushforward of algebraic cycles

`AlgebraicGeometry.AlgebraicCycle.properPushforward f c` is **the one definition** of the proper
pushforward `f_* c` of an algebraic cycle (Stacks 02R3, Fulton §1.4): Mathlib's locally finite
`AlgebraicCycle.map` with both weight functions equal to `Order.height` (the dimension of the
integral closed subscheme `closure {x}`).  A point contributes the degree `[κ(x) : κ(f x)]` of its
residue-field extension precisely when its height is preserved; contracted points receive
coefficient zero.

`dimensionProperPushforward f d` is the same map restricted to the `d`-cycles
`DimensionCycle X d = ↥(AlgebraicGeometry.cycleSubgroup X d)`; it carries no data of its own.

`FiniteDimensionPreservingResidues f` records that the residue extensions at the
height-preserving points are finite, so that Mathlib's `finrank` convention (`0` for an infinite
extension) never enters a geometric multiplicity.  It is a hypothesis of positivity statements
(`residueDegree_pos_of_dimension_eq`), **not** of the pushforward itself.

Sources: Stacks Project, Tags 02R3--02R5; the pushforward `f_*[C]` of Theorem 1.1 of the paper.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X Y : Scheme.{u}}

/-- The proper pushforward `f_* c` of an algebraic cycle (Stacks 02R3): Mathlib's
`AlgebraicCycle.map` with weights `Order.height` on both sides.  The coefficient at `y` is
`∑_{x ↦ y, height x = height y} c x · [κ(x) : κ(y)]`. -/
noncomputable def properPushforward (f : X ⟶ Y) [IsProper f] (c : AlgebraicCycle X ℤ) :
    AlgebraicCycle Y ℤ :=
  AlgebraicCycle.map f Order.height Order.height c

/-- The coefficient at an image point is the locally finite sum of source coefficients times
residue-field degrees, over the height-preserving points of the fibre. -/
theorem properPushforward_apply (f : X ⟶ Y) [IsProper f] (α : AlgebraicCycle X ℤ) (y : Y) :
    properPushforward f α y = ∑ᶠ x ∈ f ⁻¹' {y},
      α x * (if Order.height x = Order.height (f x) then (f.residueDegree x : ℤ) else 0) := by
  simp only [properPushforward, AlgebraicCycle.map, AlgebraicCycle.mapCoeff,
    Function.locallyFinsupp.map_apply, Nat.cast_ite, Nat.cast_zero]

/-- A point whose height drops is assigned coefficient zero by the pushforward. -/
theorem mapCoeff_eq_zero_of_height_lt (f : X ⟶ Y) (x : X)
    (hx : Order.height (f x) < Order.height x) :
    AlgebraicCycle.mapCoeff f (Order.height (α := X)) (Order.height (α := Y)) x = 0 := by
  simp [AlgebraicCycle.mapCoeff, ne_of_gt hx]

/-- Proper pushforward preserves the dimension index of a cycle: `f_* Z_d(X) ⊆ Z_d(Y)`. -/
theorem properPushforward_mem_cycleSubgroup_of_mem (f : X ⟶ Y) [IsProper f] (d : ℕ)
    {α : AlgebraicCycle X ℤ} (hα : α ∈ cycleSubgroup X d) :
    properPushforward f α ∈ cycleSubgroup Y d := by
  intro y hy
  rw [properPushforward_apply] at hy
  obtain ⟨x, (hxy : f x = y), hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  have hax : α x ≠ 0 := fun h => hx (by simp [h])
  have hdim : Order.height x = Order.height (f x) := by
    by_contra h
    exact hx (by simp [h])
  rw [← hxy, ← hdim]
  exact hα x hax

end AlgebraicGeometry.AlgebraicCycle

namespace AlgebraicGeometry.Intersection

variable {X Y : Scheme.{u}}

/-- Equality of point-closure dimensions (in `WithBot ℕ∞`) is equality of heights (in `ℕ∞`). -/
theorem pointClosureDimension_eq_pointClosureDimension_iff (x : X) (y : Y) :
    pointClosureDimension X x = pointClosureDimension Y y ↔ Order.height x = Order.height y :=
  WithBot.coe_inj

/-- Residue extensions are finite at the points retained by the dimension-indexed pushforward. -/
def FiniteDimensionPreservingResidues (f : X ⟶ Y) : Prop :=
  ∀ x : X, pointClosureDimension X x = pointClosureDimension Y (f x) →
    (f.residueFieldMap x).hom.Finite

/-- A dimension-preserving point has positive residue-field degree under the explicit finiteness hypothesis. -/
theorem residueDegree_pos_of_dimension_eq (f : X ⟶ Y)
    (hf : FiniteDimensionPreservingResidues f) (x : X)
    (hx : pointClosureDimension X x = pointClosureDimension Y (f x)) :
    0 < f.residueDegree x := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := hf x hx
  exact Module.finrank_pos

/-- The proper pushforward restricted to the `d`-cycles `Z_d(X) → Z_d(Y)`: the same map
`AlgebraicGeometry.AlgebraicCycle.properPushforward`, packaged with the membership proof. -/
def dimensionProperPushforward (f : X ⟶ Y) [IsProper f] (d : ℕ) (α : DimensionCycle X d) :
    DimensionCycle Y d :=
  ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward f α.1,
    AlgebraicGeometry.AlgebraicCycle.properPushforward_mem_cycleSubgroup_of_mem f d α.2⟩

@[simp]
theorem dimensionProperPushforward_coe (f : X ⟶ Y) [IsProper f] (d : ℕ) (α : DimensionCycle X d) :
    (dimensionProperPushforward f d α).1 = AlgebraicGeometry.AlgebraicCycle.properPushforward f α.1 :=
  rfl

end AlgebraicGeometry.Intersection
