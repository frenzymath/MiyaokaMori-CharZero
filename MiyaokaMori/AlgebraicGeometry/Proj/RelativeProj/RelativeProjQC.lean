import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01n2
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01no
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # The relative Proj of a graded quasi-coherent algebra sheaf

The relative Proj: a graded quasi-coherent `O_X`-algebra sheaf `S` gives a scheme `Proj_X S` over
`X`, obtained by taking `Proj` over affine opens and gluing (Stacks 01NM–01NS). This is the
construction `Y_k^GG = Proj_C 𝒮` of §2 of the paper.

`Scheme.relativeProj S` is an `abbrev` for `S.toGradedAffineAlgebra.relativeProj`, the primary
construction in `RelativeProj.lean` (index category: Mathlib's `AffineZariskiSite`; gluing via
Mathlib's `RelativeGluingData`). Being reducible, the two spellings are interchangeable for the
elaborator, `simp` and instance search.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The relative Proj of a graded quasi-coherent algebra sheaf (glued as in Stacks 01LH): the
`GradedAffineAlgebra.relativeProj` of the associated graded affine algebra
`GradedQCAlgebra.toGradedAffineAlgebra`. This is a reducible alias of the primary definition
`GradedAffineAlgebra.relativeProj`, not a second construction. -/
noncomputable abbrev AlgebraicGeometry.Scheme.relativeProj {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) : CategoryTheory.Over X :=
  S.toGradedAffineAlgebra.relativeProj

end
