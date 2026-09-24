import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The twisted affine cone

The twisted affine cone `Z ⊂ Tot(A^{⊕(N+1)})`: the closed subscheme cut out by the homogeneous
equations `F_j`, interpreted as sections of the corresponding powers of `A`, with its structure
morphism to `C`.

Reference: Definition 2.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The twisted affine cone `Z ⊂ Tot(A^{⊕(N+1)})` cut out by the homogeneous equations `F_j`, as a
scheme over `C`. -/
noncomputable def twistedAffineCone {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) : CategoryTheory.Over C :=
  CategoryTheory.Over.mk
    ((⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection A N (F j) (hF j))).subschemeι ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom)

end
