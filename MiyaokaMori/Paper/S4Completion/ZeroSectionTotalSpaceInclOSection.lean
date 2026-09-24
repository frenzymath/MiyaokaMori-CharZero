import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.TotalSpaceAgreesTotLine
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleOSection

/-! # The zero section of `Tot(L)` as the `O`-section of `P(O ⊕ L)`

Under the open immersion `Tot(L) ↪ W = P(O ⊕ L)` (`ruledSurface.totalSpaceIncl`), the zero section of
`Tot(L)` is the section of `P(O ⊕ L)` defined by the summand `O` (`AlgebraicGeometry.Scheme.oSection`).
See Corollary 4.3 of the paper (§4), where `W = P(O_C̃ ⊕ L)` is the projective
compactification of `Tot(L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Zero section ↦ `O`-section.** The zero section of `Tot(L)` composed with the open immersion
`Tot(L) ↪ P(O ⊕ L)` is the section defined by the summand `O`.

Since `totalSpaceIncl L` is `totalSpace.toProjBundle L` by definition, the claim is
`zeroSection ≫ toProjBundle = oSection`, i.e. `AlgebraicGeometry.Scheme.zeroSection_comp_toProjBundle`. -/
theorem ruledSurface.zeroSection_comp_totalSpaceIncl {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) :
    AlgebraicGeometry.Scheme.zeroSection L.toModules ≫ ruledSurface.totalSpaceIncl L =
      AlgebraicGeometry.Scheme.oSection L.toModules :=
  AlgebraicGeometry.Scheme.zeroSection_comp_toProjBundle L.toModules

end
