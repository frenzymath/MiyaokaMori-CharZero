import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AlgebraicCycles
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# A local principal contribution to an actual cycle

Mathlib exposes the order of vanishing of a rational function on a locally Noetherian integral
scheme.  This file records the corresponding contribution at one codimension-one point of an
actual `DimensionCycle`.  The result is deliberately local: the global finite-support theorem for
principal divisors, and the gluing of local equations to a Cartier divisor, are separate bridges
which are not hidden in this definition.

Thus `LocalPrincipalEquation` contains an element of the actual scheme function field together
with its nonzero proof, while `localPrincipalActionAt` returns a genuine zero-cycle obtained from
an actual one-cycle and an explicitly supplied zero-dimensional point.  The global finite-support
and Cartier gluing theorems remain separate.  No arbitrary finitely supported function is accepted
as a Cartier divisor, and no endpoint intersection equality is built into the API.

Sources: the proof of Proposition 2.4 of the paper; Stacks Project, Tags 0B8H and 0B8I; and
Mathlib's `AlgebraicGeometry.OrderOfVanishing`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Order
open scoped Classical

namespace AlgebraicGeometry.Intersection

universe u

variable {X : Scheme.{u}}

/-- A nonzero rational function at a chosen point of an integral scheme. -/
structure LocalPrincipalEquation (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (z : X) where
  function : X.functionField
  ne_zero : function ≠ 0

namespace LocalPrincipalEquation

/-- The actual codimension-one order of the rational function at the chosen point. -/
def order {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {z : X}
    (_hz : coheight z = 1) (e : LocalPrincipalEquation X z) : ℤ :=
  Scheme.ord e.function z

@[simp]
theorem order_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {z : X}
    (hz : coheight z = 1) (e : LocalPrincipalEquation X z) : e.order hz = Scheme.ord e.function z := rfl

end LocalPrincipalEquation

/-- Multiplication of genuine rational functions gives the corresponding local principal datum. -/
def LocalPrincipalEquation.mul {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (e₁ e₂ : LocalPrincipalEquation X z) : LocalPrincipalEquation X z :=
  ⟨e₁.function * e₂.function, mul_ne_zero e₁.ne_zero e₂.ne_zero⟩

/-- Order additivity for the actual function-field local equation. -/
theorem LocalPrincipalEquation.order_mul {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hz : coheight z = 1) (e₁ e₂ : LocalPrincipalEquation X z) :
    (e₁.mul e₂).order hz = e₁.order hz + e₂.order hz := by
  exact Scheme.ord_mul e₁.ne_zero e₂.ne_zero

/-- A principal local equation which is a regular unit has zero order. -/
theorem LocalPrincipalEquation.order_eq_zero_of_isUnit
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {z : X}
    (hz : coheight z = 1) (e : LocalPrincipalEquation X z) {U : X.Opens} [Nonempty U]
    {g : Γ(X, U)} (hg : IsUnit g) (hzu : z ∈ U)
    (he : X.germToFunctionField U g = e.function) : e.order hz = 0 := by
  rw [LocalPrincipalEquation.order, ← he]
  exact Scheme.ord_of_isUnit hg hzu

/-- The actual coefficient contributed by a local principal equation to a cycle at `z`. -/
def localPrincipalCoefficient {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hcurve : pointClosureDimension X (genericPoint X) = 1)
    (hz : coheight z = 1) (e : LocalPrincipalEquation X z)
    (α : DimensionCycle X 1) : ℤ :=
  e.order hz * α.1 (genericPoint X)

/-- The local principal contribution as an actual zero-dimensional algebraic cycle.

Only the selected point is retained.  The explicit `hzα` hypothesis supplies the geometric
dimension-zero support needed for the resulting `DimensionCycle X 0`; no global Cartier cap
product or principal-divisor support theorem is claimed.
-/
def localPrincipalActionAt {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hcurve : pointClosureDimension X (genericPoint X) = 1)
    (hz : coheight z = 1) (e : LocalPrincipalEquation X z)
    (α : DimensionCycle X 1) (hzα : pointClosureDimension X z = 0) : DimensionCycle X 0 :=
  ⟨Function.locallyFinsuppWithin.single z (localPrincipalCoefficient hcurve hz e α),
    isDimensionCycle_of_pointClosureDimension <| by
    intro y hy
    by_cases h : y = z
    · subst y
      exact hzα
    · exact (hy (by simp [Function.locallyFinsuppWithin.single_apply, h])).elim⟩

@[simp]
theorem localPrincipalActionAt_apply {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hcurve : pointClosureDimension X (genericPoint X) = 1)
    (hz : coheight z = 1) (e : LocalPrincipalEquation X z)
    (α : DimensionCycle X 1) (hzα : pointClosureDimension X z = 0) :
    (localPrincipalActionAt hcurve hz e α hzα).1 z = localPrincipalCoefficient hcurve hz e α := by
  simp [localPrincipalActionAt]

theorem localPrincipalActionAt_apply_of_ne {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {z y : X} (hcurve : pointClosureDimension X (genericPoint X) = 1)
    (hz : coheight z = 1)
    (e : LocalPrincipalEquation X z) (α : DimensionCycle X 1)
    (hzα : pointClosureDimension X z = 0) (hyz : y ≠ z) :
    (localPrincipalActionAt hcurve hz e α hzα).1 y = 0 := by
  simp [localPrincipalActionAt, Function.locallyFinsuppWithin.single_apply, hyz]

/-- The local contribution is coefficientwise the order of vanishing times the cycle coefficient.
-/
theorem localPrincipalCoefficient_mul {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hcurve : pointClosureDimension X (genericPoint X) = 1)
    (hz : coheight z = 1) (e₁ e₂ : LocalPrincipalEquation X z)
    (α : DimensionCycle X 1) :
    localPrincipalCoefficient hcurve hz (e₁.mul e₂) α =
      localPrincipalCoefficient hcurve hz e₁ α + localPrincipalCoefficient hcurve hz e₂ α := by
  simp only [localPrincipalCoefficient, LocalPrincipalEquation.order_mul hz, add_mul]

end AlgebraicGeometry.Intersection
