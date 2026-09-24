import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierCycleAction

/-!
# Cartier divisors from genuine local equations

This module packages a Cartier divisor by an actual open cover and nonzero elements of
the function field.  The transition condition is expressed by a unit of the structure
sheaf on every nonempty overlap, rather than by an arbitrary coefficient function.  A
finite-support witness is retained as a separate field: finiteness of the support of a
Cartier divisor is a geometric theorem in the applications, and is not silently
manufactured by this definition.

For a one-dimensional integral scheme whose codimension-one points are closed, the
resulting order function gives an actual zero-dimensional algebraic cycle.  This is the
input needed by the later global Cartier action and degree-comparison constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical

namespace AlgebraicGeometry.Intersection

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A unit ratio on an open set, formulated using genuine sections of the structure sheaf.

The `Nonempty` argument handles empty overlaps without introducing a spurious global
section.  On a nonempty overlap the ratio is required to be the image of a unit section
under the actual map to the function field.
-/
def IsUnitRatioOn (U : X.Opens) (f g : X.functionField) : Prop :=
  ∀ (hU : Nonempty U),
    letI : Nonempty U := hU
    ∃ u : Γ(X, U), IsUnit u ∧ X.germToFunctionField U u = f / g

/-- Local equations and unit transition data for a Cartier divisor on an integral scheme. -/
structure CartierLocalData (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] where
  index : Type u
  opens : index → X.Opens
  cover : ⋃ i, (opens i : Set X) = Set.univ
  locallyFinite : LocallyFinite (fun i ↦ (opens i : Set X))
  equation : index → X.functionField
  equation_ne_zero : ∀ i, equation i ≠ 0
  ratio_unit : ∀ i j, IsUnitRatioOn (opens i ⊓ opens j) (equation i) (equation j)

namespace CartierLocalData

/-- A chosen member of the cover containing a point.  The choice is independent of the
resulting order because transition ratios are units; that independence is recorded by
`coefficient_eq_of_mem` below and does not enter the definition as arbitrary data. -/
def indexAt (D : CartierLocalData X) (x : X) : D.index :=
  let hx : x ∈ ⋃ i, (D.opens i : Set X) := by
    rw [D.cover]
    exact Set.mem_univ x
  Classical.choose (Set.mem_iUnion.mp hx)

theorem indexAt_mem (D : CartierLocalData X) (x : X) : x ∈ D.opens (D.indexAt x) := by
  let hx : x ∈ ⋃ i, (D.opens i : Set X) := by
    rw [D.cover]
    exact Set.mem_univ x
  exact Classical.choose_spec (Set.mem_iUnion.mp hx)

/-- The local principal equation selected at a point of the cover. -/
def localEquationAt (D : CartierLocalData X) (x : X) : LocalPrincipalEquation X x :=
  ⟨D.equation (D.indexAt x), D.equation_ne_zero _⟩

@[simp]
theorem localEquationAt_function (D : CartierLocalData X) (x : X) :
    (D.localEquationAt x).function = D.equation (D.indexAt x) := rfl

/-- The order coefficient of the Cartier divisor at a codimension-one point. -/
def coefficient (D : CartierLocalData X) (x : X) : ℤ :=
  if hx : coheight x = 1 then Scheme.ord (D.equation (D.indexAt x)) x else 0

@[simp]
theorem coefficient_eq_ord (D : CartierLocalData X) (x : X)
    (hx : coheight x = 1) : D.coefficient x =
      Scheme.ord (D.equation (D.indexAt x)) x := by
  simp [coefficient, hx]

@[simp]
theorem coefficient_eq_zero_of_coheight_ne_one (D : CartierLocalData X) (x : X)
    (hx : coheight x ≠ 1) : D.coefficient x = 0 := by
  simp [coefficient, hx]

/- Multiplying the unit ratio by the denominator equation recovers the numerator equation;
the order of the ratio vanishes at every point of the overlap. -/
theorem coefficient_eq_of_mem (D : CartierLocalData X) (x : X)
    (hx : coheight x = 1) (i j : D.index)
    (hxi : x ∈ D.opens i) (hxj : x ∈ D.opens j) :
    Scheme.ord (D.equation i) x = Scheme.ord (D.equation j) x := by
  have hU : Nonempty ↑(D.opens i ⊓ D.opens j) :=
    ⟨⟨x, hxi, hxj⟩⟩
  letI : Nonempty ↑(D.opens i ⊓ D.opens j) := hU
  obtain ⟨s, hs, hratio⟩ := D.ratio_unit i j hU
  have hxu : x ∈ D.opens i ⊓ D.opens j := ⟨hxi, hxj⟩
  have hunit : Scheme.ord (D.equation i / D.equation j) x = 0 := by
    rw [← hratio]
    exact Scheme.ord_of_isUnit hs hxu
  calc
    Scheme.ord (D.equation i) x =
        Scheme.ord ((D.equation i / D.equation j) * D.equation j) x := by
      rw [div_mul_cancel₀ _ (D.equation_ne_zero j)]
    _ = Scheme.ord (D.equation i / D.equation j) x +
        Scheme.ord (D.equation j) x :=
      Scheme.ord_mul (x := x)
        (div_ne_zero (D.equation_ne_zero i) (D.equation_ne_zero j)) (D.equation_ne_zero j)
    _ = Scheme.ord (D.equation j) x := by rw [hunit, zero_add]

end CartierLocalData

/-- A Cartier divisor together with a genuine finite-support witness for its order function. -/
structure FiniteCartierDivisor (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] extends CartierLocalData X where
  finite_support : (Function.support toCartierLocalData.coefficient).Finite

namespace FiniteCartierDivisor

@[simp]
theorem coefficient_eq_ord (D : FiniteCartierDivisor X) (x : X)
    (hx : coheight x = 1) : D.toCartierLocalData.coefficient x =
      Scheme.ord (D.equation (D.indexAt x)) x :=
  D.toCartierLocalData.coefficient_eq_ord x hx

/-- A one-dimensional Cartier divisor has a zero-dimensional order cycle once the support
points are known to be closed.  The closedness condition is explicit because an arbitrary
integral Noetherian scheme may have higher-dimensional codimension-one closures. -/
structure ZeroDimensionalSupport (D : FiniteCartierDivisor X) : Prop where
  pointClosureDimension_zero : ∀ x, D.toCartierLocalData.coefficient x ≠ 0 →
    pointClosureDimension X x = 0

/-- The actual zero cycle attached to a finite-support Cartier divisor. -/
def zeroCycle (D : FiniteCartierDivisor X) (hD : D.ZeroDimensionalSupport) :
    DimensionCycle X 0 :=
  ⟨{
      toFun := D.toCartierLocalData.coefficient
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := by
        intro x _
        exact ⟨Set.univ, Filter.univ_mem, by simpa using D.finite_support⟩ },
    isDimensionCycle_of_pointClosureDimension fun x hx => hD.pointClosureDimension_zero x hx⟩

@[simp]
theorem zeroCycle_apply (D : FiniteCartierDivisor X) (hD : D.ZeroDimensionalSupport)
    (x : X) : (D.zeroCycle hD).1 x = D.toCartierLocalData.coefficient x := rfl

theorem zeroCycle_support_finite (D : FiniteCartierDivisor X)
    (hD : D.ZeroDimensionalSupport) :
    (Function.support (D.zeroCycle hD).1).Finite := by
  simpa [zeroCycle] using D.finite_support

end FiniteCartierDivisor

end AlgebraicGeometry.Intersection
