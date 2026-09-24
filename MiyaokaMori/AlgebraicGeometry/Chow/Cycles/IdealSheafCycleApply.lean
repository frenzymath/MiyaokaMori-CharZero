import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qu
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ClosedImmersionPushforwardRatEquiv

/-! # Pointwise coefficients of the cycle of a closed subscheme

The pointwise coefficients of the cycle `[Z]_d = ι_*([Z]_d^Z)` of a closed subscheme
(`IdealSheafData.cycle`, Stacks 02QU): at an image point `ι z′` it equals the coefficient of `[Z]_d^Z` at
`z′` (the fiber of a closed immersion is a single point, the residue degree is `1` and the height is
preserved); outside `supp Z = range ι` it is `0`.

Source: Stacks 02QU, 02R3 (coefficients of the pushforward along a closed immersion).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
  (I : X.IdealSheafData)

/-- `[Z]_d = ι_*([Z]_d^Z)`, with Mathlib's pushforward on the right. The locally Noetherian instance is
given as an argument (a `Prop`, equal by proof irrelevance to the instance inside the body of
`IdealSheafData.cycle`); the equality holds by definition. -/
theorem cycle_eq_properPushforward' [AlgebraicGeometry.IsLocallyNoetherian I.subscheme] (d : ℕ) :
    I.cycle d = AlgebraicGeometry.AlgebraicCycle.properPushforward I.subschemeι (I.subscheme.fundamentalCycle d) :=
  rfl

/-- The coefficient of `[Z]_d` at an image point `ι z′` equals the coefficient of `[Z]_d^Z` at `z′`. -/
theorem cycle_apply_subschemeι [AlgebraicGeometry.IsLocallyNoetherian I.subscheme] (d : ℕ)
    (z' : I.subscheme) :
    I.cycle d (I.subschemeι.base z') = I.subscheme.fundamentalCycle d z' := by
  rw [I.cycle_eq_properPushforward' d]
  exact MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply _ _ _

/-- The coefficient of `[Z]_d` vanishes outside `supp Z`. -/
theorem cycle_apply_of_notMem_support (d : ℕ) {z : X} (hz : z ∉ I.support) :
    I.cycle d z = 0 := by
  have : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  rw [I.cycle_eq_properPushforward' d]
  refine MiyaokaMori.ClosedImmersionPushforward.properPushforward_apply_of_notMem_range _ _ ?_
  rwa [I.range_subschemeι]

end AlgebraicGeometry.Scheme.IdealSheafData

end
