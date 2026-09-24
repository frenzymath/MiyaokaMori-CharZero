import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.PushforwardPreservesDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors

/-! # Graded proper pushforward of cycles on varieties

The graded proper pushforward `f_* : Z_i(X) → Z_i(Y)` as a homomorphism of additive groups (the
pushforward `f_*` of Theorem 1.1 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The intersection of a fiber of a proper (quasi-compact) morphism with the support of a cycle is finite:
the argument used by Mathlib to define `Function.locallyFinsupp.map` (take a quasi-compact open
neighbourhood `U` of `y`; `f⁻¹U` is quasi-compact). -/
private theorem finite_fiber_inter_support {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] (c : AlgebraicGeometry.AlgebraicCycle X ℤ) (y : Y) :
    (f.base ⁻¹' {y} ∩ Function.support (c : X → ℤ)).Finite := by
  obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
    (by simp : y ∈ (Set.univ : Set Y)) isOpen_univ
  refine (c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (f.isSpectralMap.2 hU.1.1 hU.1.2)).subset ?_
  refine Set.inter_subset_inter_left _ ?_
  rintro z (hz : f.base z = y)
  have hzU : f.base z ∈ U := hz ▸ hU.2.1
  exact hzU

/-- The pushforward of cycles (Mathlib's `AlgebraicCycle.map`) is additive in the coefficients. -/
theorem AlgebraicGeometry.AlgebraicCycle.map_add {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (a b : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.map f wx wy (a + b) =
      AlgebraicGeometry.AlgebraicCycle.map f wx wy a +
        AlgebraicGeometry.AlgebraicCycle.map f wx wy b := by
  ext y
  show (∑ᶠ x ∈ f.base ⁻¹' {y}, (a x + b x) *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f wx wy x : ℕ) : ℤ)) =
    (∑ᶠ x ∈ f.base ⁻¹' {y}, a x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f wx wy x : ℕ) : ℤ)) +
    (∑ᶠ x ∈ f.base ⁻¹' {y}, b x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f wx wy x : ℕ) : ℤ))
  have hfin : ∀ c : AlgebraicGeometry.AlgebraicCycle X ℤ,
      (f.base ⁻¹' {y} ∩ Function.support fun x => c x *
        ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f wx wy x : ℕ) : ℤ)).Finite := by
    intro c
    refine (finite_fiber_inter_support f c y).subset ?_
    refine Set.inter_subset_inter_right _ ?_
    intro x hx
    exact fun h => hx (by simp [h])
  rw [← finsum_mem_add_distrib' (hfin a) (hfin b)]
  exact finsum_mem_congr rfl fun x _ => by ring

/-- The pushforward of cycles sends the zero cycle to the zero cycle. -/
theorem AlgebraicGeometry.AlgebraicCycle.map_zero {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N) :
    AlgebraicGeometry.AlgebraicCycle.map f wx wy (0 : AlgebraicGeometry.AlgebraicCycle X ℤ) = 0 := by
  ext y
  show (∑ᶠ x ∈ f.base ⁻¹' {y}, (0 : ℤ) *
    ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f wx wy x : ℕ) : ℤ)) = 0
  simp

/-- The underlying scheme of `X` with the `k`-structure induced by `f` and the structure morphism of `Y`:
still a `k`-variety (integrality is unchanged; separatedness and finite type follow from `f` proper
composed with the variety `Y`), for which `f` is a `k`-morphism. Used to reduce an `f` that need not be a
`k`-morphism to the `k`-morphism case. -/
private def sourceVariety {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] : Variety k where
  carrier := X.carrier
  «over» := ⟨f ≫ Y.structureMorphism⟩
  integral := X.integral
  separated := inferInstanceAs (AlgebraicGeometry.IsSeparated (f ≫ Y.structureMorphism))
  finiteType := ({ toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance } :
    AlgebraicGeometry.IsOfFiniteType (f ≫ Y.structureMorphism))

/-- A proper morphism between varieties satisfies the predicate `FiniteDimensionPreservingResidues` (the
residue field extension is finite at dimension-preserving points).

`f` need not be a `k`-morphism: replacing the `k`-structure of the source by `sourceVariety f` (the one
induced from `Y` through `f`), `X` is still a `k`-variety and `f` becomes a `k`-morphism; `Order.height`
and `residueFieldMap` depend only on the underlying schemes and `f`, so
`properPushforward_residueField_finite` (Stacks 02R4) applies directly. -/
theorem Variety.finiteDimensionPreservingResidues {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] :
    AlgebraicGeometry.Intersection.FiniteDimensionPreservingResidues f := by
  intro x hx
  have hh : Order.height x = Order.height (f.base x) := by
    rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height X.toScheme x,
      AlgebraicGeometry.Intersection.pointClosureDimension_eq_height Y.toScheme (f.base x)] at hx
    exact_mod_cast hx
  exact @properPushforward_residueField_finite k _ (sourceVariety f) Y f ⟨rfl⟩ x hh

/-- The graded proper pushforward `f_* : Z_i(X) → Z_i(Y)` as a homomorphism of additive groups. At the level
of cycles it is `AlgebraicGeometry.AlgebraicCycle.properPushforward` (Mathlib's `AlgebraicCycle.map` with
weights `Order.height`); it lands in `Z_i(Y)` by `properPushforward_mem_cycleGroup`, and additivity is
`AlgebraicCycle.map_add`. -/
noncomputable def cyclePushforward {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] (i : ℕ) :
    CycleGroup X i →+ CycleGroup Y i where
  toFun c := ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward f c.1,
    properPushforward_mem_cycleGroup f c.1 c.2⟩
  map_zero' := Subtype.ext (AlgebraicGeometry.AlgebraicCycle.map_zero f _ _)
  map_add' a b := Subtype.ext (AlgebraicGeometry.AlgebraicCycle.map_add f _ _ a.1 b.1)

end
