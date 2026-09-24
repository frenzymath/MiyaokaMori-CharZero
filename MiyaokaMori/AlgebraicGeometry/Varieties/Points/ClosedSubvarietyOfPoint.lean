import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne

/-! # Every point of a variety is the generic point of a closed subvariety

For any point `x` of a variety `X`, the closure `{x}⁻` with its reduced induced closed subscheme
structure is an integral closed subscheme `V` whose generic point maps to `x` and whose image is
`{x}⁻`; when `x` has height `1` (`dim {x}⁻ = 1`), `V` is one-dimensional.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Every point of a variety is the image of the generic point of a closed subvariety, and a point
of height `1` gives a one-dimensional closed subvariety. -/
theorem ClosedSubvariety.exists_of_point {k : Type u} [Field k] {X : Variety k} (x : X.toScheme) :
    ∃ V : ClosedSubvariety X,
      V.ι.base (genericPoint V.carrier) = x ∧
      Set.range V.ι.base = closure ({x} : Set X.toScheme) ∧
      (Order.height x = 1 → SchemeIsOneDimensional V.carrier) := by
  refine ⟨ClosedSubvariety.ofPoint x, ClosedSubvariety.genericPt_ofPoint x, ?_, ?_⟩
  · exact AlgebraicGeometry.Intersection.ReducedPointClosure.range_inclusion X.toScheme x
  · intro hx
    exact (AlgebraicGeometry.Intersection.ReducedPointClosure.dimension_eq X.toScheme x).trans <| by
      simp [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height, hx]

end
