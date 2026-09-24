import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt

/-! # Nonvanishing locus versus `IsZeroAt`

`x ∈ X_s ⟺ ¬ IsZeroAt s x`: the membership condition of `nonvanishingLocus` and the definition of
`IsZeroAt` coincide verbatim (Stacks 01CY); it is stated here as a rewritable lemma, to translate
between the definition of `IsAmple` (which uses `nonvanishingLocus`) and
`IsAmple.eventually_globallyGenerated` (01Q3, which uses `IsZeroAt`).

The statement `X_{g^*t} = g⁻¹(Y_t)` (`nonvanishingLocus_sectionPullbackAlong`) is in
`Stacks0c4k_IsAmplePullbackIso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `x ∈ X_s ⟺ ¬ IsZeroAt s x` (both sides are the same by definition). -/
theorem AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iff_not_isZeroAt
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) (x : X) :
    x ∈ L.nonvanishingLocus s ↔ ¬ IsZeroAt s x := by
  rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
  rfl

end
