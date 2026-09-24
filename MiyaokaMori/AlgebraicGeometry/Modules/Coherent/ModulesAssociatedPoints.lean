import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk

/-! # Associated points and embedded points of a sheaf of modules

`x` is an associated point of `F` if the maximal ideal `m_x` of the stalk lies in
`Ass_{O_{X,x}}(F_x)` (the definition of Stacks in the locally Noetherian case). `F` has no embedded
associated points if any two associated points `x ⤳ y` (`y` a specialization of `x`) satisfy `x = y`,
i.e. no associated point is a proper specialization of another. A scheme `X` has no embedded points if
the structure sheaf `O_X` has no embedded associated points.

Source: Stacks 05AI, 02OI, 02OE (Divisors: associated points, embedded points).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `x` is an associated point of `F`: `m_x ∈ Ass_{O_{X,x}}(F_x)`. -/
def AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint {X : AlgebraicGeometry.Scheme.{u}}
    (F : X.Modules) (x : X) : Prop :=
  IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈ associatedPrimes (X.presheaf.stalk x) (F.stalk x)

/-- `F` has no embedded associated points: there is no proper specialization between associated
points. -/
def AlgebraicGeometry.Scheme.Modules.HasNoEmbeddedAssociatedPoints {X : AlgebraicGeometry.Scheme.{u}}
    (F : X.Modules) : Prop :=
  ∀ x y : X, AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint F x →
    AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint F y → x ⤳ y → x = y

/-- A scheme has no embedded points if its structure sheaf has no embedded associated points. -/
def AlgebraicGeometry.Scheme.HasNoEmbeddedPoints (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  AlgebraicGeometry.Scheme.Modules.HasNoEmbeddedAssociatedPoints
    (SheafOfModules.unit X.ringCatSheaf : X.Modules)

end
