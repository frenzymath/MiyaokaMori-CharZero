import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseTower
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeAdditivity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Proper pushforward preserves the degree of an actual zero cycle

The support of a zero cycle consists of closed points. A proper morphism sends those points
to closed points, so the dimension branch in the existing proper pushforward retains every
contributing point. Its residue-field weights multiply with the target's base-field weights
by the scalar tower for the original structure maps. Finite support then permits regrouping
the sum by fibres, including cancellation, negative coefficients, and empty support.

No new cycle or degree evaluator is constructed here: the statements are about
`AlgebraicGeometry.AlgebraicCycle.properPushforward` and `rawZeroCycleDegree`.
The raw finrank identity is stated without finiteness assumptions (`Module.finrank_mul_finrank`
needs none); its use for cycle degree has finite extensions from properness at the closed support
points. The additivity corollaries `rawZeroCycleDegree_properPushforward_add` / `_finsetSum` /
`_weightedSum` follow the main theorem.

Sources: Stacks Project, `chow.tex`, `definition-proper-pushforward`,
`lemma-compose-pushforward`, `definition-degree-zero-cycle`, and
`lemma-spell-out-degree-zero-cycle`; Theorem 1.1 of the paper.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry AlgebraicGeometry.Proj AlgebraicGeometry.Intersection
open scoped Classical BigOperators

universe u

namespace AlgebraicGeometry.Intersection

/-- Proper maps preserve the closure dimension at every point supporting a zero cycle. -/
theorem zeroCycle_pointClosureDimension_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (β : DimensionCycle X 0) (x : X) (hx : β.1 x ≠ 0) :
    pointClosureDimension X x = pointClosureDimension Y (f x) := by
  have hclosed : IsClosed ({x} : Set X) :=
    isClosed_singleton_of_pointClosureDimension_zero x
      (IsDimensionCycle.pointClosureDimension_eq β.2 x hx)
  have himage : IsClosed ({f x} : Set Y) := by
    simpa only [Set.image_singleton] using f.isClosedMap _ hclosed
  exact (IsDimensionCycle.pointClosureDimension_eq β.2 x hx).trans
    (pointClosureDimension_eq_zero_of_isClosed (f x) himage).symm

/-- Finranks multiply for the actual residue-field maps and their specified base-field maps. -/
theorem residueFieldDegree_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : X) :
    residueFieldDegree (f ≫ p) x = residueFieldDegree p (f x) * f.residueDegree x := by
  let Xb : SchemeOver k := ⟨X, f ≫ p⟩
  let Yb : SchemeOver k := ⟨Y, p⟩
  let : Algebra k (Y.residueField (f x)) := (pointBaseMap p (f x)).hom.toAlgebra
  let : Algebra k (X.residueField x) := (pointBaseMap (f ≫ p) x).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (Y.residueField (f x)) (X.residueField x) :=
    residueFieldBase_isScalarTower (X := Xb) (Y := Yb) f rfl x
  change Module.finrank k (X.residueField x) =
    Module.finrank k (Y.residueField (f x)) *
      Module.finrank (Y.residueField (f x)) (X.residueField x)
  exact (Module.finrank_mul_finrank k (Y.residueField (f x)) (X.residueField x)).symm

/-- The proper pushforward coefficient is a finite fibre sum over any set containing the support. -/
theorem zeroCycle_properPushforward_eq_sum_on {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (β : DimensionCycle X 0)
    (s : Finset X) (hs : ∀ x, x ∉ s → β.1 x = 0) (y : Y) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f β.1 y =
      ∑ x ∈ s with f x = y, β.1 x * (f.residueDegree x : ℤ) := by
  calc
    AlgebraicGeometry.AlgebraicCycle.properPushforward f β.1 y =
        ∑ x ∈ s with f x = y, β.1 x *
          (if Order.height x = Order.height (f x)
            then (f.residueDegree x : ℤ) else 0) := by
      rw [AlgebraicGeometry.AlgebraicCycle.properPushforward_apply]
      apply finsum_mem_eq_sum_of_subset
      · intro x hx
        have hβx : β.1 x ≠ 0 := fun h ↦ hx.2 (by simp [h])
        apply Finset.mem_filter.mpr
        refine ⟨?_, hx.1⟩
        by_contra hxs
        exact hβx (hs x hxs)
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
    _ = ∑ x ∈ s with f x = y, β.1 x * (f.residueDegree x : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : β.1 x = 0
      · simp [hx]
      · rw [if_pos ((pointClosureDimension_eq_pointClosureDimension_iff x (f x)).mp
          (zeroCycle_pointClosureDimension_map_eq f β x hx))]

/-- Proper pushforward preserves the existing residue-weighted degree over the same field. -/
theorem rawZeroCycleDegree_properPushforward
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X ⟶ Y) [IsProper f]
    (β : DimensionCycle X 0) :
    rawZeroCycleDegree p (dimensionProperPushforward f 0 β) =
      rawZeroCycleDegree (f ≫ p) β := by
  let s := (properCycle_finiteSupport (f ≫ p) β.1).toFinset
  have hs : ∀ x, x ∉ s → β.1 x = 0 := by
    intro x hx
    by_contra hβx
    exact hx ((properCycle_finiteSupport (f ≫ p) β.1).mem_toFinset.mpr hβx)
  have hpush : ∀ y, y ∉ s.image f → (dimensionProperPushforward f 0 β).1 y = 0 := by
    intro y hy
    change AlgebraicGeometry.AlgebraicCycle.properPushforward f β.1 y = 0
    rw [zeroCycle_properPushforward_eq_sum_on f β s hs]
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨hxs, hxy⟩ := Finset.mem_filter.mp hx
    exact (hy (hxy ▸ Finset.mem_image_of_mem f hxs)).elim
  rw [rawZeroCycleDegree_eq_sum_on p _ (s.image f) hpush,
    rawZeroCycleDegree_eq_sum_on (f ≫ p) β s hs]
  calc
    (∑ y ∈ s.image f,
        (dimensionProperPushforward f 0 β).1 y * (residueFieldDegree p y : ℤ)) =
        ∑ y ∈ s.image f, ∑ x ∈ s with f x = y,
          (β.1 x * (f.residueDegree x : ℤ)) * (residueFieldDegree p y : ℤ) := by
      apply Finset.sum_congr rfl
      intro y _
      change AlgebraicGeometry.AlgebraicCycle.properPushforward f β.1 y *
        (residueFieldDegree p y : ℤ) = _
      rw [zeroCycle_properPushforward_eq_sum_on f β s hs, Finset.sum_mul]
    _ = ∑ y ∈ s.image f, ∑ x ∈ s with f x = y,
        β.1 x * (residueFieldDegree (f ≫ p) x : ℤ) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x hx
      have hxy : f x = y := (Finset.mem_filter.mp hx).2
      rw [← hxy, residueFieldDegree_comp p f x, Nat.cast_mul]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = ∑ x ∈ s, β.1 x * (residueFieldDegree (f ≫ p) x : ℤ) :=
      Finset.sum_fiberwise_of_maps_to (fun x hx ↦ Finset.mem_image_of_mem f hx) _

/-- Proper pushforward transport commutes with addition of actual zero cycles. -/
theorem rawZeroCycleDegree_properPushforward_add
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X ⟶ Y) [IsProper f]
    (β γ : DimensionCycle X 0) :
    rawZeroCycleDegree p
        (dimensionProperPushforward f 0 (DimensionCycle.add β γ)) =
      rawZeroCycleDegree (f ≫ p) β + rawZeroCycleDegree (f ≫ p) γ := by
  rw [rawZeroCycleDegree_properPushforward p f, rawZeroCycleDegree_add]

/-- Proper pushforward transport commutes with finite sums of actual zero cycles. -/
theorem rawZeroCycleDegree_properPushforward_finsetSum
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X ⟶ Y) [IsProper f]
    {ι : Type u} (s : Finset ι) (β : ι → DimensionCycle X 0) :
    rawZeroCycleDegree p
        (dimensionProperPushforward f 0 (DimensionCycle.finsetSum s β)) =
      ∑ i ∈ s, rawZeroCycleDegree (f ≫ p) (β i) := by
  rw [rawZeroCycleDegree_properPushforward p f, rawZeroCycleDegree_finsetSum]

/-- Proper pushforward transport retains integer coefficients in finite weighted sums. -/
theorem rawZeroCycleDegree_properPushforward_weightedSum
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X ⟶ Y) [IsProper f]
    {ι : Type u} (s : Finset ι) (n : ι → ℤ) (β : ι → DimensionCycle X 0) :
    rawZeroCycleDegree p
        (dimensionProperPushforward f 0 (DimensionCycle.weightedSum s n β)) =
      ∑ i ∈ s, n i * rawZeroCycleDegree (f ≫ p) (β i) := by
  rw [rawZeroCycleDegree_properPushforward p f, rawZeroCycleDegree_weightedSum]

/-- A closed immersion preserves raw zero-cycle degree. -/
theorem rawZeroCycleDegree_closedImmersion
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (i : X ⟶ Y) [IsClosedImmersion i] (β : DimensionCycle X 0) :
    rawZeroCycleDegree p (dimensionProperPushforward i 0 β) =
      rawZeroCycleDegree (i ≫ p) β :=
  rawZeroCycleDegree_properPushforward p i β

end AlgebraicGeometry.Intersection
