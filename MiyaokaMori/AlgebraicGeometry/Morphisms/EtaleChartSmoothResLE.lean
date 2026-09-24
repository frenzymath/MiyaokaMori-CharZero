import MiyaokaMori.Prelude

/-! # Smoothness restricted to a smaller open

Restricting smoothness to a smaller open: if `Zx.ι ≫ p` is smooth of relative dimension `n`,
`V ≤ Zx` and `V ≤ p⁻¹U`, then `p.resLE U V` is smooth of relative dimension `n` (used for the étale
charts of the based jet space, §2.2 of the paper: `V → U` is smooth of relative dimension `n+1` as a
composition with an open immersion).
Mathlib: `SmoothOfRelativeDimension n` has `HasRingHomProperty`, hence is Zariski-local on the source
and on the target and stable under base change.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of relative dimension `n` passes to `resLE`.** If `Zx.ι ≫ p : Zx ⟶ S` is smooth
of relative dimension `n` and `V ≤ Zx`, `V ≤ p ⁻¹ᵁ U`, then `p.resLE U V : V ⟶ U` is smooth of
relative dimension `n`.

Proof. `V.ι ≫ p = Z.homOfLE _ ≫ (Zx.ι ≫ p)` and the property is local at the source
(`IsZariskiLocalAtSource.comp`), so `V.ι ≫ p` has it. Then `V.ι ≫ p = p.resLE U V ≫ U.ι` with
`U.ι` an open immersion, and a property stable under base change can be cancelled against
post-composition with an open immersion (`MorphismProperty.of_postcomp`).

Note (toolchain pitfall): with the default `backward.isDefEq.respectTransparency = true` the
instances `IsZariskiLocalAtSource / IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)` coming
from `HasRingHomProperty` are **not** found by `inferInstance`; Mathlib itself switches the option
off locally, and so do we here. -/
theorem AlgebraicGeometry.smoothOfRelativeDimension_resLE_of_le {Z S : AlgebraicGeometry.Scheme.{u}}
    (p : Z ⟶ S) (Zx : Z.Opens) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension n (Zx.ι ≫ p)] (U : S.Opens) (V : Z.Opens)
    (hVZx : V ≤ Zx) (hVU : V ≤ p ⁻¹ᵁ U) :
    AlgebraicGeometry.SmoothOfRelativeDimension n (p.resLE U V hVU) := by
  have h1 : AlgebraicGeometry.SmoothOfRelativeDimension n (V.ι ≫ p) := by
    rw [← AlgebraicGeometry.Scheme.homOfLE_ι Z hVZx, Category.assoc]
    exact AlgebraicGeometry.IsZariskiLocalAtSource.comp ‹_› _
  have : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.SmoothOfRelativeDimension.{u} n) :=
    AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange n
  refine MorphismProperty.of_postcomp (W := @AlgebraicGeometry.SmoothOfRelativeDimension n)
    (W' := @AlgebraicGeometry.IsOpenImmersion) _ U.ι inferInstance ?_
  rw [AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  exact h1

end
