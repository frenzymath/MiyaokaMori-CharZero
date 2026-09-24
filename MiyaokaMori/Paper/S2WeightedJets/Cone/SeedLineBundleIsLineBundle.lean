import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackLineBundlePow
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace

/-! # The seed line bundle is a line bundle

The seed line bundle `A = f^*O_X(1)` is a line bundle: `O_{ℙ^N}(1)` is a line bundle, and the pullback
of a line bundle along a morphism is a line bundle (applied twice) (§2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `seedLineBundle e f = f^*(e.emb^*O_{ℙ^N}(1))` is a line bundle: `O(1)` is a line bundle
(`projectiveSpaceTwist_isLineBundle`), and the pullback of a line bundle is a line bundle (twice). -/
instance seedLineBundle_isLineBundle {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (f : C ⟶ X) : (seedLineBundle e f).IsLineBundle := by
  unfold seedLineBundle ProjectiveEmbedding.oX
  infer_instance

end
