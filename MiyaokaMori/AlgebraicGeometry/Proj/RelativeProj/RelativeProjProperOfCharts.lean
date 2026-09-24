import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Properness of the relative Proj from properness of the charts

Statement: the structure morphism `Proj_X S → X` of the relative Proj of a graded quasi-coherent
algebra `S` is proper as soon as every chart
`projToOpen U : Proj S(U) → U` (`U` affine open) is proper.

Reason: properness is Zariski-local on the target (Mathlib `IsZariskiLocalAtTarget @IsProper`), and
the chart square `projChart_isPullback U` identifies `π⁻¹(U) → U` with `projToOpen U`
(Stacks 01NQ). Used for Stacks 01WC.

Source: Stacks 01W2 (morphisms-lemma-proper-local-on-the-base) + Stacks 01NQ.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- Properness of `Proj_X S → X` from properness of every chart `Proj S(U) → U`. -/
theorem relativeProj_hom_isProper_of_projToOpen
    (h : ∀ U : X.AffineZariskiSite, IsProper (S.projToOpen U)) :
    IsProper S.relativeProj.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (AffineZariskiSite.directedCover X)
  intro U
  have hpb : IsPullback (S.projChart U) (S.projToOpen U) S.relativeProj.hom U.toOpens.ι :=
    (S.projChart_isPullback U).flip
  change IsProper (pullback.snd S.relativeProj.hom U.toOpens.ι)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) hpb.isoPullback.hom,
    hpb.isoPullback_hom_snd]
  exact h U

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
