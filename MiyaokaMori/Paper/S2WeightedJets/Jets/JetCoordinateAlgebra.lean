import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSchemeAffineOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The coordinate algebra of the based jet scheme

The coordinate algebra `S` of `J_k^s`: the quasi-coherent `O_C`-algebra with `J_k^s = Spec_C S` (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The coordinate algebra `S := π_* O_J` of `J_k^s` (`π : J_k^s → C` is affine), so that `J_k^s ≅ Spec_C S`. -/

noncomputable def jetCoordinateAlgebra {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    C.QCAlgebra :=
  AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf (relativeJetScheme (k := k) Z s hs r).hom

end
