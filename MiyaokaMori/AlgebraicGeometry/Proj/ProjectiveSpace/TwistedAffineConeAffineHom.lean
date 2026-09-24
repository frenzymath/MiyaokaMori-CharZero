import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone

/-! # The twisted affine cone is affine over `C`

The twisted affine cone is affine over `C`: `Z → Tot(A^{⊕(N+1)})` is a closed immersion (affine),
`Tot = Spec_C Sym` is affine over `C`, and the composite is affine.

Reference: §2 of the paper (`Tot` is affine over `C`; `Z` is a closed subscheme of it, Definition 2.1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance twistedAffineCone_isAffineHom {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    AlgebraicGeometry.IsAffineHom (twistedAffineCone A N deg F hF).hom := by
  -- hom = I.subschemeι ≫ (relativeSpec _).hom: a closed immersion (affine) followed by the
  -- structure morphism of a relative Spec (affine)
  dsimp only [twistedAffineCone, CategoryTheory.Over.mk_hom, AlgebraicGeometry.Scheme.totalSpace]
  infer_instance

end
