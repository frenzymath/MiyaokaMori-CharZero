import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueLift
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Equality of morphisms to a separated scheme on a scheme-theoretically dense open

Stacks Project, Tag 01RH (morphisms-lemma-equality-of-morphisms): let `Y → S` be separated, `f, g : X → Y`
`S`-morphisms and `U ⊆ X` an open whose scheme-theoretic closure is `X` (the kernel ideal sheaf of `U.ι` is
zero); if `f|_U = g|_U` then `f = g`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Stacks 01RH. "The scheme-theoretic closure of `U` in `X` is `X`" is expressed as: the kernel ideal sheaf
   of the open immersion `U.ι` is zero, `U.ι.ker = ⊥` (the scheme-theoretic image is `V(ker)`; Mathlib's
   `Scheme.Hom.ker` is the ideal sheaf of the scheme-theoretic image for any morphism).
   "`f, g` are `S`-morphisms and `Y → S` is separated" follows Mathlib's `ext_of_isDominant_of_isSeparated`:
   `s : Y ⟶ S` separated and `f ≫ s = g ≫ s`. -/

theorem AlgebraicGeometry.Scheme.Hom.ext_of_ker_ι_eq_bot {X Y S : AlgebraicGeometry.Scheme.{u}}
    {f g : X ⟶ Y} (s : Y ⟶ S) [AlgebraicGeometry.IsSeparated s] (h : f ≫ s = g ≫ s)
    (U : X.Opens) (hU : U.ι.ker = ⊥) (hfg : U.ι ≫ f = U.ι ≫ g) : f = g := by
  let X' : CategoryTheory.Over S := CategoryTheory.Over.mk (f ≫ s)
  let Y' : CategoryTheory.Over S := CategoryTheory.Over.mk s
  let f' : X' ⟶ Y' := CategoryTheory.Over.homMk f
  let g' : X' ⟶ Y' := CategoryTheory.Over.homMk g h.symm
  let ι' : CategoryTheory.Over.mk (U.ι ≫ f ≫ s) ⟶ X' := CategoryTheory.Over.homMk U.ι
  have hl : ι' ≫ f' = ι' ≫ g' := by ext1; exact hfg
  have : AlgebraicGeometry.IsSeparated Y'.hom := ‹_›
  have hker : (equalizer.ι f' g').left.ker = ⊥ := le_bot_iff.mp <|
    (AlgebraicGeometry.Scheme.Hom.le_ker_comp (equalizer.lift ι' hl).left _).trans
      (by rw [← CategoryTheory.Over.comp_left, equalizer.lift_ι]; exact hU.le)
  have := AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq (equalizer.ι f' g').left (𝟙 X)
    (equalizer.ι f' g').left (by simp) (by rw [hker, AlgebraicGeometry.Scheme.Hom.ker_eq_bot_of_isIso])
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

end
