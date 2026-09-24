import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistPiApp

/-! # The chart comparison map of the twisting sheaf is an isomorphism

Statement (Stacks 01LI / 01NR): the chart comparison map `twistChartHom m U : ι_U^* O(m) ⟶ O_U(m)`
(`RelativeProjTwistLimit`; the adjoint transpose of the limit projection `twistπ m U`) is an
isomorphism, for every chart `U : X.AffineZariskiSite`; `twistChartIso` is the resulting isomorphism.

Proof:
1. `twistChartHom m U = (pullback ι_U).map (twistπ m U) ≫ counit` (`Adjunction.homEquiv_counit`).
2. The counit of `pullback ι_U ⊣ pushforward ι_U` is an isomorphism because `pushforward ι_U` is fully faithful for
   the open immersion `ι_U` (Mathlib instances `Scheme.Modules.instFullPushforward…` and
   `Adjunction.counit_isIso_of_R_fully_faithful`).
3. `(pullback ι_U).map (twistπ m U)` is an isomorphism iff `(restrictFunctor ι_U).map (twistπ m U)` is
   (`NatIso.isIso_map_iff` along `restrictFunctorIsoPullback`), and the latter is
   `isIso_restrictFunctor_map_twistπ` (the actual content of Stacks 01LI).

Compile note: a version going through `restrictAdjunction` with `change`/`rfl` steps made the kernel spend 23–27 s
per declaration unfolding the adjunction data (`Adjunction.homEquiv`, `leftAdjointUniq`) down to sections. Only
`rw` with fully instantiated equations is used now; `Proj.twist` is kept irreducible as a guard.

Source: Stacks 01LI, 01NR; Lemma 2.2 of the paper.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

-- Guard (as in `RelativeProjTwistLimit`): `O_U(m)` is treated as an opaque module sheaf here.
attribute [local irreducible] AlgebraicGeometry.Proj.twist

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- The pullback of the limit projection to the chart is an isomorphism (transport of
`isIso_restrictFunctor_map_twistπ` along `restrictFunctorIsoPullback`). -/
theorem isIso_pullback_map_twistπ (m : ℤ) (U : X.AffineZariskiSite) :
    IsIso ((Scheme.Modules.pullback (S.projChart U)).map (S.twistπ m U)) :=
  (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (S.projChart U)) (S.twistπ m U)).mp
    (S.isIso_restrictFunctor_map_twistπ m U)

/-- `twistChartHom` is `(pullback ι_U).map (twistπ m U)` followed by the counit. -/
theorem twistChartHom_eq_comp (m : ℤ) (U : X.AffineZariskiSite) :
    S.twistChartHom m U =
      (Scheme.Modules.pullback (S.projChart U)).map (S.twistπ m U) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (S.projChart U)).counit.app
          (Proj.twist (S.grading U) m) := by
  rw [twistChartHom, Adjunction.homEquiv_counit]

/-- **Stacks 01LI / 01NR**: the chart comparison `ι_U^* O(m) ⟶ O_U(m)` is an isomorphism. -/
theorem isIso_twistChartHom (m : ℤ) (U : X.AffineZariskiSite) : IsIso (S.twistChartHom m U) := by
  rw [twistChartHom_eq_comp]
  have := S.isIso_pullback_map_twistπ m U
  infer_instance

/-- `ι_U^* O(m) ≅ O_U(m)` (Stacks 01NR). The data is `twistChartHom`; only `IsIso` is a proof obligation. -/
def twistChartIso (m : ℤ) (U : X.AffineZariskiSite) :
    (Scheme.Modules.pullback (S.projChart U)).obj (S.twist m) ≅ Proj.twist (S.grading U) m :=
  haveI := S.isIso_twistChartHom m U
  asIso (S.twistChartHom m U)

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
