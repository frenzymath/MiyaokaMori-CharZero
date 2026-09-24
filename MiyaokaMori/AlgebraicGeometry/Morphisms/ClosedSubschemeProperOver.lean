import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Closed subschemes of a proper `k`-scheme are proper

A closed subscheme `e : Z ⟶ X` of a scheme `X` proper over `k` (regarded as a `k`-scheme through
`e`) is proper over `k`: a closed immersion is finite, hence proper, and a composition of proper
morphisms is proper (Stacks Project, Tags 01W6 and 01W1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem isProperOver_of_closedImmersion {k : Type u} [Field k] {X Z : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (e : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion e] :
    letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨e ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    IsProperOver k Z := by
  change AlgebraicGeometry.IsProper
    (e ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  let _ : AlgebraicGeometry.IsProper
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  infer_instance

end
