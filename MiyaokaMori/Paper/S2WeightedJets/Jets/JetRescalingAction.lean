import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingActionAffineLine
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingActionConstruction

/-! # The rescaling action on the jet scheme

The `𝔾_m`-action on `J_k^s` induced by `t ↦ λt` (preserving `C` and fixing the constant term `s`; §2 of the paper).

The construction `jetRescalingAction : GmActionOver k (relativeJetScheme Z s hs r)` together with all its axioms
(`jetRescalingAction_point_prop` / `_act_over` / `_one_act` / `_mul_act`) lives in `JetRescalingActionConstruction`;
the extension of the action to the monoid `𝔸¹ = Spec k[λ]` (`affineLineRescalingAct`, restricting to
`jetRescalingAction` along `𝔾_m ↪ 𝔸¹`) is `JetRescalingActionAffineLine`. This module assembles the non-negativity
theorem from the two; all declarations of those modules are re-exported through the imports.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `G_m`-rescaling action on `J_r^s(Z/C)` is non-negative: it extends to an action of the monoid
`A¹ = Spec k[λ]` (the coaction `t ↦ λ ⊗ t` lands in `O[λ]`, not only in `O[λ^{±1}]`).  Witness:
`affineLineRescalingAct` with `affineLineRescalingAct_restrict` (`jetRescalingAction_isNonnegative'`).
§2 of the paper (the nonnegative grading by parameter rescaling). -/
theorem jetRescalingAction_isNonnegative {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    (jetRescalingAction (k := k) Z s hs r).IsNonnegative :=
  jetRescalingAction_isNonnegative' (k := k) Z s hs r

end
