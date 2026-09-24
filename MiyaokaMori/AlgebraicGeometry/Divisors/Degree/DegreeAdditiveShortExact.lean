import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegreeEqLineBundleDegreeDet
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DetOfShortExact
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.Stacks0ayx

/-! # Additivity of the degree in short exact sequences

For a short exact sequence `0 → F → G → H → 0` of vector bundles on a smooth projective curve,
`deg G = deg F + deg H` (multiplicativity of `det` and additivity of the degree of line bundles).
Used for `deg E = d` in (2.3) of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Degrees are additive in short exact sequences of vector bundles on a smooth projective curve. -/
theorem VectorBundle.degree_add_of_shortExact {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {S : CategoryTheory.ShortComplex C.toScheme.Modules}
    (hS : S.ShortExact) (F G H : AlgebraicGeometry.VectorBundle C.toVariety)
    (eF : F.toModules ≅ S.X₁) (eG : G.toModules ≅ S.X₂) (eH : H.toModules ≅ S.X₃) :
    VectorBundle.degree G = VectorBundle.degree F + VectorBundle.degree H := by
  rw [VectorBundle.degree_eq_lineBundle_degree_det G,
    VectorBundle.degree_eq_lineBundle_degree_det F,
    VectorBundle.degree_eq_lineBundle_degree_det H]
  obtain ⟨e⟩ := VectorBundle.det_of_shortExact hS F G H eF eG eH
  exact LineBundle.degree_eq_add_of_iso_tensor _ _ _ e

end
