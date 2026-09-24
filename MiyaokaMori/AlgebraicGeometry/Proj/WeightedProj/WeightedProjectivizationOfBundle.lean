import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra

/-! # Weighted projectivization of a family of vector bundles

The weighted projectivization of a family of vector bundles with prescribed weights: the relative
Proj of the weighted symmetric algebra `Sym(V_0^∨ ⊕ ⋯ ⊕ V_{r−1}^∨)` (with `V_q^∨` in weight `q+1`),
parametrizing the (weighted) lines in the fibers. The convention is "projectivization of lines"
(the paper's `P_lines`: the coefficient blocks take values in `E`, the coordinate functions lie in
`E^∨`), i.e. `Proj Sym(V^∨)` in the notation of Hartshorne/Stacks, not `Proj Sym(V)`. This is the
split weighted projectivization `Y^sp` of the reduction to a split weighted bundle in the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The weighted projectivization `Proj_X Sym(⊕_q (V q)^∨)` of the bundles `V q`, with `(V q)^∨` in
weight `q + 1`, as a scheme over `X`. -/
noncomputable def AlgebraicGeometry.Scheme.weightedProjBundle {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) (hV : ∀ q, (V q).IsLocallyFree)
    [∀ q, (V q).IsFiniteType] :
    CategoryTheory.Over X :=
  haveI := hV
  AlgebraicGeometry.Scheme.relativeProj
    (AlgebraicGeometry.Scheme.weightedSymAlgebra V)

-- `weightedSymAlgebra V = Sym(⊕_q (V q)^∨)`: the coordinate functions of the `q`-th factor
-- (`q = 0, …, r−1`) have weight `q+1`; projectivization of lines (generators taken from `V^∨`).

end
