import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition

/-! # The twisting sheaf on a relative Proj: transition maps

The twisting sheaf `S.twist m : S.relativeProj.left.Modules` of a relative Proj, that is
`O_{Proj_X S}(m)` obtained by gluing (Stacks 01LI, 01NP): the sheaves `O(m)` on the charts
`Proj S(U)` (`Proj.twist`) are pushed forward along the open immersions `projChart U`; for
`U ≤ V` the transition map is the ring-level map `Proj.twistPushTransition`
(`θ_f : O_V(m) → r_* O_U(m)` composed with the pushforward and the transport of equalities),
and `S.twist m` is the limit of this diagram indexed by `X.AffineZariskiSiteᵒᵖ`.

Because `Proj.twist` is built on homogeneous localizations, every transport of equalities
requires many definitional-equality checks; to keep compile times manageable the
construction is split over three modules: this one gives the transition maps and their
unit law, `RelativeProjTwistComp` gives transitivity, and `RelativeProjTwistLimit` gives the
diagram, its limit and the chart comparison maps.

Design notes:
* The transition maps use `twistPushTransition` (`θ_f`) directly and need no isomorphism
  between twists of different Proj's, so the definition and its functoriality are purely
  constructive.
* The index category is Mathlib's `AffineZariskiSite`, the same one used for `relativeProj`.

Sources: Stacks 01LI, 01NP; Lemma 2.2 of the paper.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- The transition map `(ι_V)_* O_V(m) → (ι_U)_* O_U(m)` for `U ≤ V`. -/
def twistTransition (m : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V) :
    (Scheme.Modules.pushforward (S.projChart V)).obj (Proj.twist (S.grading V) m) ⟶
      (Scheme.Modules.pushforward (S.projChart U)).obj (Proj.twist (S.grading U) m) :=
  Proj.twistPushTransition (S.restrictGraded h) (S.restrict_irrelevant_le h) m
    (S.projChart V) (S.projChart U) (S.map_projChart h)

theorem twistTransition_id (m : ℤ) (U : X.AffineZariskiSite) :
    S.twistTransition m (le_refl U) = 𝟙 _ :=
  Proj.twistPushTransition_id _ _ m
    (congrArg (fun f : S.grading U →+*ᵍ S.grading U =>
      (f : S.toAffineAlgebra.sections U →+* S.toAffineAlgebra.sections U))
      (S.restrictGraded_refl U)) _ _

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
