import MiyaokaMori.Prelude

/-! # Coherent sheaves

A coherent sheaf: quasi-coherent and locally finitely generated (locally a quotient of a free sheaf
of finite rank). On a locally Noetherian scheme this is the usual notion of coherence.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A sheaf of modules is coherent if it is quasi-coherent and of finite type. -/
class AlgebraicGeometry.Scheme.Modules.IsCoherent {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) : Prop where
  quasicoherent : M.IsQuasicoherent
  finiteType : M.IsFiniteType

-- On a Noetherian scheme, coherent = quasi-coherent + finite type.

end
