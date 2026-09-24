import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphismFactorsThroughPoint

/-! # Closed points over an algebraically closed field have residue field `k`

For a closed point `x` of a scheme `X` locally of finite type over an algebraically closed field `k`,
`κ(x) = k` (Mathlib `residueFieldIsoBase`). Consequently:
1. `k`-morphisms to `Spec κ(x)` are unique: if `a, b : S → Spec κ(x)` agree after composing with the
   structure morphism, then `a = b` (`Spec κ(x) → Spec k` is an isomorphism, hence can be cancelled);
2. two `k`-morphisms from a reduced scheme `S` to `X` whose underlying maps are both constant with value `x`
   are equal (both factor as `S → Spec κ(x) → X` by `ConstantMorphismFactorsThroughPoint`, then use (1));
3. `k`-morphisms send closed points to closed points (closed points ↔ `k`-points, Mathlib
   `pointEquivClosedPoint`).

Source: Mathlib `AlgebraicGeometry.AlgClosed.Basic` (closed points correspond to `k`-points). Used in the
proof of Theorem 4.2 of the paper: a constant map on a ruling fiber equals the seed point
`f(ρ(y))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- (1) A morphism to `Spec κ(x)` is determined by its composite with the `k`-structure morphism (`κ(x) = k`). -/
theorem AlgebraicGeometry.eq_of_comp_fromSpecResidueField_comp_eq {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgebraicGeometry.Scheme.{u}} (str : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType str] (x : X) (hx : IsClosed ({x} : Set X))
    {S : AlgebraicGeometry.Scheme.{u}} (a b : S ⟶ AlgebraicGeometry.Spec (X.residueField x))
    (h : a ≫ X.fromSpecResidueField x ≫ str = b ≫ X.fromSpecResidueField x ≫ str) : a = b := by
  rw [← AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv str x hx] at h
  exact (cancel_mono _).mp h

/-- (2) Two `k`-morphisms from a reduced scheme to `X`, both constant with value the closed point `x`, are equal. -/
theorem AlgebraicGeometry.eq_of_constant_at_closedPoint {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgebraicGeometry.Scheme.{u}} (str : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType str] (x : X) (hx : IsClosed ({x} : Set X))
    {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsReduced S] (a b : S ⟶ X)
    (ha : ∀ s : S, a.base s = x) (hb : ∀ s : S, b.base s = x)
    (h : a ≫ str = b ≫ str) : a = b := by
  obtain ⟨a', ha'⟩ := factors_through_residueField_of_isConstant a x ha
  obtain ⟨b', hb'⟩ := factors_through_residueField_of_isConstant b x hb
  have : a' = b' := by
    apply AlgebraicGeometry.eq_of_comp_fromSpecResidueField_comp_eq str x hx
    rw [← Category.assoc, ha', ← Category.assoc, hb']
    exact h
  rw [← ha', ← hb', this]

/-- (3) A `k`-morphism between `k`-schemes locally of finite type sends closed points to closed points. -/
theorem AlgebraicGeometry.isClosed_singleton_image_of_isClosed_singleton {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : AlgebraicGeometry.Scheme.{u}}
    (strY : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType strY]
    (strX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType strX]
    (g : Y ⟶ X) (hg : g ≫ strX = strY) (y : Y) (hy : IsClosed ({y} : Set Y)) :
    IsClosed ({g.base y} : Set X) := by
  let q : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X := AlgebraicGeometry.pointOfClosedPoint strY y hy ≫ g
  have hq : q ≫ strX = 𝟙 _ := by
    simp only [q, Category.assoc, hg, AlgebraicGeometry.pointOfClosedPoint_comp]
  have hmem : IsClosed ({q (IsLocalRing.closedPoint k)} : Set X) :=
    (AlgebraicGeometry.pointEquivClosedPoint strX ⟨q, hq⟩).2
  have hpt : q (IsLocalRing.closedPoint k) = g y :=
    congrArg g (AlgebraicGeometry.pointOfClosedPoint_apply strY y hy _)
  rwa [hpt] at hmem

end
