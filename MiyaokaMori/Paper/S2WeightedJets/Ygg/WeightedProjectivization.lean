import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC

/-! # The weighted projectivization of the based jets

`Y_k^GG = Proj_C S_k` and its structure morphism `π_k : Y_k^GG ⟶ C`, where `S_k` is the graded
algebra of the relative based jets (§2.2 of the paper). Only the rescaling of the jet
parameter is quotiented out, not the full group of reparametrizations.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The weighted projectivization `Y_k^GG = Proj_C S_k` of the relative based `r`-jets of `Z`
along the section `s`, as a scheme over `C`. -/
noncomputable abbrev weightedJetProjectivization {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    CategoryTheory.Over C :=
  AlgebraicGeometry.Scheme.relativeProj (jetGradedAlgebra (k := k) Z s hs r).1

/-- The structure morphism `π_k : Y_k^GG ⟶ C`. -/
noncomputable def weightedJetProjection {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) : (weightedJetProjectivization (k := k) Z s hs r).left ⟶ C :=
  (weightedJetProjectivization (k := k) Z s hs r).hom

end
