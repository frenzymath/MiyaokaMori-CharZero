import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Length
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Sober
import Mathlib.Order.KrullDimension

/-!
# Generic multiplicities and dimension-indexed algebraic cycles

The multiplicity at a generic point is the actual module length of the local ring over itself.
Extended natural coefficients retain this length before its finiteness theorem is proved; in
particular no conversion sends an unproved infinite length to the integer zero. The local support
condition follows from the proved finiteness of the set of generic points of a Noetherian scheme.

Integer lifts specify every coefficient, including its sign. They are properties of actual
Mathlib algebraic cycles, not extra multiplicity data. Finiteness and integer-lift existence
are separate results, not constructions supplied by this module. The scheme-theoretic fibre
cycles of Lemma 5.1 of the paper are an intended application.

Sources: Stacks Project, Tags 02QR, 02QT and 02QU.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators Classical

namespace AlgebraicGeometry.Intersection

universe u

/-- The dimension of the irreducible closed subset represented by a scheme point,
`dim closure {x}`.

This is only notation for the one primitive Mathlib provides for the dimension of a point:
`Order.height x : ℕ∞`, the height of `x` in the specialization preorder of `X`
(`AlgebraicGeometry.Scheme` carries `instance : Preorder X := specializationPreorder X`),
coerced into `WithBot ℕ∞`. It is an `abbrev`, not a second definition of dimension. The formula
`topologicalKrullDim (closure {x})` is the theorem
`pointClosureDimension_eq_topologicalKrullDim_closure` below. -/
abbrev pointClosureDimension (X : Scheme.{u}) (x : X) : WithBot ℕ∞ :=
  ((Order.height x : ℕ∞) : WithBot ℕ∞)

/-- Every irreducible component has the specified dimension. The empty scheme is allowed. -/
def IsPureDimension (X : Scheme.{u}) (d : ℕ) : Prop :=
  ∀ x ∈ genericPoints X, pointClosureDimension X x = d

/-! ### Point dimension is `Order.height`

`Order.height x : ℕ∞` (specialization order) is the primitive notion of the dimension of a point;
`pointClosureDimension` is the same number read in `WithBot ℕ∞` through the Krull dimension of the
closure. The two lemmas below live here so that every module defining a `d`-cycle
can convert. Proof: `C = closure {x}` is closed, hence quasi-sober and T0, so
`IrreducibleCloseds C ≃o C` (`irreducibleSetEquivPoints`); as an ordered set `C = Set.Iic x`
(`y ∈ closure {x} ↔ x ⤳ y ↔ y ≤ x`), and `Order.height_eq_krullDim_Iic`. -/

theorem _root_.topologicalKrullDim_closure_singleton_eq_height {α : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] (x : α) :
    topologicalKrullDim (closure ({x} : Set α))
      = ((@Order.height α (specializationPreorder α) x : ℕ∞) : WithBot ℕ∞) := by
  let oα : Preorder α := specializationPreorder α
  have : QuasiSober (closure ({x} : Set α)) :=
    (isClosed_closure.isClosedEmbedding_subtypeVal).quasiSober
  have hmem : ∀ a : α, a ∈ closure ({x} : Set α) ↔ a ∈ Set.Iic x := fun a =>
    specializes_iff_mem_closure.symm
  let e : @OrderIso (closure ({x} : Set α)) (Set.Iic x)
      (specializationOrder (closure ({x} : Set α))).toLE _ :=
    { toFun := fun a => ⟨a.1, (hmem _).mp a.2⟩
      invFun := fun a => ⟨a.1, (hmem _).mpr a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := fun {a b} =>
        show (b : α) ⤳ (a : α) ↔ b ⤳ a from (subtype_specializes_iff b a).symm }
  rw [topologicalKrullDim, Order.height_eq_krullDim_Iic]
  exact @Order.krullDim_eq_of_orderIso _ _ _ _
    (@OrderIso.trans _ _ _ _ (specializationOrder (closure ({x} : Set α))).toLE _
      irreducibleSetEquivPoints e)

/-- The closure dimension of a scheme point is its `Order.height` (read in `WithBot ℕ∞`).
Since `pointClosureDimension` is an `abbrev` of the right-hand side (item 4) this is `rfl`; the name
is kept because downstream proofs rewrite with it. -/
theorem pointClosureDimension_eq_height (X : Scheme.{u}) (x : X) :
    pointClosureDimension X x = ((Order.height x : ℕ∞) : WithBot ℕ∞) :=
  rfl

/-- The point dimension is the topological Krull dimension of the closure of the point (item 4). Use this to pass between the
`Order.height` primitive and closure-of-point computations. -/
theorem pointClosureDimension_eq_topologicalKrullDim_closure (X : Scheme.{u}) (x : X) :
    pointClosureDimension X x = topologicalKrullDim (closure ({x} : Set X)) :=
  (topologicalKrullDim_closure_singleton_eq_height x).symm

/-- **The** coercion lemma for comparing a `ℕ`-indexed dimension with a point dimension: the
`WithBot ℕ∞` equation `pointClosureDimension X x = d` and the `ℕ∞` equation `Order.height x = d`
say the same thing. Every `ℕ` ↔ `ℕ∞` ↔ `WithBot ℕ∞` comparison of a point dimension goes through
this lemma. -/
theorem pointClosureDimension_eq_natCast_iff (X : Scheme.{u}) (x : X) (d : ℕ) :
    pointClosureDimension X x = (d : WithBot ℕ∞) ↔ Order.height x = (d : ℕ∞) := by
  rw [pointClosureDimension_eq_height]
  exact_mod_cast Iff.rfl

/-! ### The group of `d`-cycles `Z_d(X)`

`AlgebraicGeometry.cycleSubgroup X d` is **the one definition** of the `d`-cycles: the additive
subgroup of Mathlib's `AlgebraicCycle X ℤ` of cycles supported on points of `Order.height = d`
(a point `x` ↔ the integral closed subscheme `closure {x}`, of dimension `height x`).
`IsDimensionCycle` and `DimensionCycle` below are aliases with no content of their own. -/

/-- `Z_d(X)`: the algebraic cycles supported in dimension exactly `d`. -/
def _root_.AlgebraicGeometry.cycleSubgroup (X : Scheme.{u}) (i : ℕ) :
    AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {c | ∀ x : X, c x ≠ 0 → Order.height x = (i : ℕ∞)}
  add_mem' := by
    intro a b ha hb x hx
    by_cases h : a x = 0
    · exact hb x (by simpa [h] using hx)
    · exact ha x h
  zero_mem' := fun _ hx => (hx rfl).elim
  neg_mem' := by
    intro a ha x hx
    exact ha x (by simpa using hx)

theorem _root_.AlgebraicGeometry.mem_cycleSubgroup_iff {X : Scheme.{u}} {i : ℕ}
    (c : AlgebraicCycle X ℤ) :
    c ∈ AlgebraicGeometry.cycleSubgroup X i ↔ ∀ x : X, c x ≠ 0 → Order.height x = (i : ℕ∞) :=
  Iff.rfl

/-- Membership in `Z_d(X)` read through `pointClosureDimension` (the `WithBot ℕ∞` form used by the
`AlgebraicGeometry.Intersection` constructions). -/
theorem _root_.AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension {X : Scheme.{u}}
    {i : ℕ} (c : AlgebraicCycle X ℤ) :
    c ∈ AlgebraicGeometry.cycleSubgroup X i ↔
      ∀ x : X, c x ≠ 0 → pointClosureDimension X x = (i : WithBot ℕ∞) :=
  forall_congr' fun x => imp_congr_right fun _ =>
    (pointClosureDimension_eq_natCast_iff X x i).symm

/-- An actual integral algebraic cycle is concentrated in dimension `d`: alias for membership in
`Z_d(X) = AlgebraicGeometry.cycleSubgroup X d` (no separate condition). -/
abbrev IsDimensionCycle (X : Scheme.{u}) (d : ℕ) (α : AlgebraicCycle X ℤ) : Prop :=
  α ∈ AlgebraicGeometry.cycleSubgroup X d

/-- Integral `d`-cycles: alias for the coercion of `Z_d(X)` to a type (no separate carrier). -/
abbrev DimensionCycle (X : Scheme.{u}) (d : ℕ) :=
  ↥(AlgebraicGeometry.cycleSubgroup X d)

/-- The height of a point carrying a nonzero coefficient of a `d`-cycle. -/
theorem IsDimensionCycle.height_eq {X : Scheme.{u}} {d : ℕ} {α : AlgebraicCycle X ℤ}
    (hα : IsDimensionCycle X d α) (x : X) (hx : α x ≠ 0) : Order.height x = (d : ℕ∞) :=
  hα x hx

/-- The closure dimension of a point carrying a nonzero coefficient of a `d`-cycle. -/
theorem IsDimensionCycle.pointClosureDimension_eq {X : Scheme.{u}} {d : ℕ}
    {α : AlgebraicCycle X ℤ} (hα : IsDimensionCycle X d α) (x : X) (hx : α x ≠ 0) :
    pointClosureDimension X x = (d : WithBot ℕ∞) :=
  (AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension α).mp hα x hx

/-- Build a `d`-cycle from the `pointClosureDimension` form of the support condition. -/
theorem isDimensionCycle_of_pointClosureDimension {X : Scheme.{u}} {d : ℕ}
    {α : AlgebraicCycle X ℤ} (h : ∀ x : X, α x ≠ 0 → pointClosureDimension X x = (d : WithBot ℕ∞)) :
    IsDimensionCycle X d α :=
  (AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension α).mpr h

/-- The actual length of a local ring as a module over itself, retaining a possible infinity. -/
def stalkLength (X : Scheme.{u}) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)

/-- A closed subscheme's stalk length measured over its ambient local ring. -/
def closedSubschemeStalkLength {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) : ℕ∞ := by
  letI : Algebra (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    (i.stalkMap z).hom.toAlgebra
  exact Module.length (X.presheaf.stalk (i z)) (Z.presheaf.stalk z)

/-- Surjectivity of the closed immersion's stalk map preserves the actual module length. -/
theorem closedSubschemeStalkLength_eq {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) : closedSubschemeStalkLength i z = stalkLength Z z := by
  let : Algebra (X.presheaf.stalk (i z)) (Z.presheaf.stalk z) :=
    (i.stalkMap z).hom.toAlgebra
  exact Module.length_eq_of_surjective (i.stalkMap_surjective z)

/-- Generic multiplicity is the local-ring length at component generic points and zero elsewhere. -/
def fundamentalMultiplicity (X : Scheme.{u}) (x : X) : ℕ∞ :=
  if x ∈ genericPoints X then stalkLength X x else 0

@[simp]
theorem fundamentalMultiplicity_of_generic (X : Scheme.{u}) (x : X)
    (hx : x ∈ genericPoints X) : fundamentalMultiplicity X x = stalkLength X x := by
  simp [fundamentalMultiplicity, hx]

@[simp]
theorem fundamentalMultiplicity_of_not_generic (X : Scheme.{u}) (x : X)
    (hx : x ∉ genericPoints X) : fundamentalMultiplicity X x = 0 := by
  simp [fundamentalMultiplicity, hx]

/-- Noetherian schemes have only finitely many nonzero generic multiplicities. -/
theorem fundamentalMultiplicity_finiteSupport (X : Scheme.{u}) [IsNoetherian X] :
    (Function.support (fundamentalMultiplicity X)).Finite := by
  apply (genericPoints.finite
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))).subset
  intro x hx
  by_contra hn
  exact hx (fundamentalMultiplicity_of_not_generic X x hn)

/-- The fundamental cycle with extended natural coefficients, before proving finite length. -/
def extendedFundamentalCycle (X : Scheme.{u}) [IsNoetherian X] : AlgebraicCycle X ℕ∞ where
  toFun := fundamentalMultiplicity X
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ :=
    ⟨Set.univ, Filter.univ_mem, by simpa using fundamentalMultiplicity_finiteSupport X⟩

@[simp]
theorem extendedFundamentalCycle_apply (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    extendedFundamentalCycle X x = fundamentalMultiplicity X x := rfl

/-- The finite set of component generic points, with its actual Noetherian finiteness proof. -/
def componentGenericPoints (X : Scheme.{u}) [IsNoetherian X] : Finset X :=
  (genericPoints.finite
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))).toFinset

@[simp]
theorem mem_componentGenericPoints (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    x ∈ componentGenericPoints X ↔ x ∈ genericPoints X := by
  simp [componentGenericPoints]

/-- The closed subscheme's extended cycle in its actual ambient scheme, with every generic length.

For a closed immersion `i : Z ⟶ X`, no residue-field degree occurs: the residue-field maps are
isomorphisms. The length used here is over `𝒪_Z`; the comparison with `𝒪_X` is a separate theorem.
-/
def extendedClosedSubschemeCycle {Z X : Scheme.{u}} [IsNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] : AlgebraicCycle X ℕ∞ :=
  ∑ η ∈ componentGenericPoints Z,
    Function.locallyFinsuppWithin.single (i η) (stalkLength Z η)

/-- At an embedded component generic point the ambient cycle retains the entire local length. -/
theorem extendedClosedSubschemeCycle_apply_generic {Z X : Scheme.{u}} [IsNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (η : Z) (hη : η ∈ genericPoints Z) :
    extendedClosedSubschemeCycle i (i η) = stalkLength Z η := by
  simp only [extendedClosedSubschemeCycle, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply, Function.locallyFinsuppWithin.single_apply,
    i.isClosedEmbedding.injective.eq_iff]
  simp [Finset.sum_ite_eq, mem_componentGenericPoints, hη]

/-- An integral cycle lifts an extended cycle when all its nonnegative coefficients agree.

The nonnegativity clause makes the `Int.toNat` comparison faithful; an infinite extended
coefficient admits no integer lift. This definition neither assumes nor chooses a lift.
-/
def IsIntegralCycleLift {X : Scheme.{u}} (β : AlgebraicCycle X ℕ∞)
    (α : AlgebraicCycle X ℤ) : Prop :=
  ∀ x : X, 0 ≤ α x ∧ ((α x).toNat : ℕ∞) = β x

/-- Any two integral lifts of the same extended cycle agree coefficient by coefficient. -/
theorem IsIntegralCycleLift.unique {X : Scheme.{u}} {β : AlgebraicCycle X ℕ∞}
    {α γ : AlgebraicCycle X ℤ} (hα : IsIntegralCycleLift β α)
    (hγ : IsIntegralCycleLift β γ) : α = γ := by
  apply DFunLike.ext
  intro x
  have hnat : (α x).toNat = (γ x).toNat := by
    exact_mod_cast (hα x).2.trans (hγ x).2.symm
  have hint := congrArg (fun n : ℕ ↦ (n : ℤ)) hnat
  simpa only [Int.toNat_of_nonneg (hα x).1, Int.toNat_of_nonneg (hγ x).1] using hint

end AlgebraicGeometry.Intersection
