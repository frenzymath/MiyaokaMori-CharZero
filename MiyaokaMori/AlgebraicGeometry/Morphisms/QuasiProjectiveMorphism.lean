import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Quasi-projective morphisms

A morphism `f` is quasi-projective (Stacks Project, Tag 01VW) if it is of finite type and there is an
`f`-relatively ample invertible sheaf (on every affine open `V` of the base, `L` restricted to
`f⁻¹(V)` is ample).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

class AlgebraicGeometry.IsQuasiProjectiveMorphism {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) : Prop where
  locallyOfFiniteType : AlgebraicGeometry.LocallyOfFiniteType f
  quasiCompact : AlgebraicGeometry.QuasiCompact f
  exists_relativelyAmple : ∃ (L : X.Modules) (_ : L.IsLineBundle),
    ∀ V : S.affineOpens, AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj L)

end
