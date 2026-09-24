import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTerm
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone

/-! # Representability of the relative based jet functor

The jet functor based at `s` is representable (for `Z` affine over `C`): locally
`J_k^s = Spec O(U)[a_{α,q}]/(coefficients of t^1, …, t^k after substituting s + Σ a_q t^q into the equations of Z)`,
glued by Stacks 01JJ (§2 of the paper: the based relative jet scheme and the local form `s + a_1 t + ⋯ + a_k t^k` of
a based jet satisfying the cone equations modulo `t^{k+1}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Immediate from the representability data `relativeJetScheme.representableBy` (the glued `relativeJetScheme` and
the bijection `homEquiv`). -/

theorem relativeJetFunctor_isRepresentable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    (relativeJetFunctor (k := k) Z s hs r).IsRepresentable :=
  (relativeJetScheme.representableBy (k := k) Z s hs r).isRepresentable

end
