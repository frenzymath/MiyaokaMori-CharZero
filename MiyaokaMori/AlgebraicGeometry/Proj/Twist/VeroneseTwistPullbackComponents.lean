import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjVeroneseIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullbackTwistToPushforwardIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseTwistPullbackVeroneseHomApp

/-! # Chart-level components of the Veronese twist comparison

The chart-level building blocks of the isomorphism of gluing diagrams in `VeroneseTwistPullback` (see its module
docstring for the route): for an affine open `U` of `X`, with
`ψ := (leftIso S m hm).hom : Proj_X S^(m) ⟶ Proj_X S`, `c_U`, `c'_U` the charts and `e_U := chartIso S m hm U`,
* the chart square `c'_U ≫ ψ = e_U.hom ≫ c_U` (`projChart_comp_leftIso_hom`);
* `twistChartPushIso : ψ_* c'_U_* T' ≅ c_U_* (e_U.hom)_* T'` (`pushforwardComp`/`pushforwardCongr`);
* `chartTwistPushIsoVeronese : (e_U.hom)_* O_{A'(U)}(n) ≅ (v_U.hom)_* O_{B(U)}(n)` (step 3a,
  `VeroneseTwistPullbackTwistToPushforwardIso`);
* the component `twistDiagramComponentIso Ψ U` of the diagram isomorphism, given the degree-rescaling isomorphisms `Ψ_U`;
* `chartTwistHom U`, the degree-rescaling comparison morphism `(v_U.hom)_* O_{B(U)}(1) ⟶ O_{A(U)}(m)`
  (`Proj.veroneseTwistHom`, `VeroneseTwistPullbackVeroneseComparison`, with the hypotheses supplied by
  `VeroneseTwistPullbackVeroneseHomApp`).

Kept separate from `VeroneseTwistPullback` so that the naturality proof (`VeroneseTwistPullbackChartIsoNatural`) and
the assembly compile quickly.

Source: Stacks 0B5J, 01MX, 01NP; Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj.veroneseIso

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m)

/-- **Chart square**: `c'_U ≫ ψ.hom = e_U.hom ≫ c_U`, where
`ψ = leftIso S m hm = HasColimit.isoOfNatIso (natIso S m hm)`, `c_U = colimit.ι _ U` and `natIso.hom.app U = e_U.hom`
(`HasColimit.isoOfNatIso_ι_hom`). -/
theorem projChart_comp_leftIso_hom (U : X.AffineZariskiSite) :
    (S.veronese m).toGradedAffineAlgebra.projChart U ≫ (leftIso S m hm).hom =
      (chartIso S m hm U).hom ≫ S.toGradedAffineAlgebra.projChart U := by
  -- `HasColimit` is found for `projGluingData.functor` (via `IsLocallyDirected`), not for the syntactically
  -- different `projFunctor`; `HasColimit` is a proposition, so any instance will do.
  have : HasColimit (S.veronese m).toGradedAffineAlgebra.projFunctor :=
    inferInstanceAs (HasColimit (S.veronese m).toGradedAffineAlgebra.projGluingData.functor)
  have : HasColimit S.toGradedAffineAlgebra.projFunctor :=
    inferInstanceAs (HasColimit S.toGradedAffineAlgebra.projGluingData.functor)
  exact HasColimit.isoOfNatIso_ι_hom (natIso S m hm) U

/-- `e_U.hom = Proj.map ofVeronese_U ≫ (Proj.veroneseIso A(U) m hm).hom` (definitional; `chartIso` is `Iso.trans`). -/
theorem chartIso_hom (U : X.AffineZariskiSite) :
    (chartIso S m hm U).hom =
      AlgebraicGeometry.Proj.map (ofVeronese S m hm U.toOpens) (irrelevant_le_map_ofVeronese S m hm U.toOpens) ≫
        (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom := rfl

/-- **Components** (step 2): `(ψ.hom)_* (c'_U)_* T' ≅ (c_U)_* (e_U.hom)_* T'` for any module `T'` on the chart
`Proj A^{(m)}(U)`: `pushforwardComp`, `pushforwardCongr` along the chart square, `pushforwardComp.symm`. -/
def twistChartPushIso (U : X.AffineZariskiSite) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso S m hm).hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward ((S.veronese m).toGradedAffineAlgebra.projChart U)).obj
          (AlgebraicGeometry.Proj.twist ((S.veronese m).sectionsGrading U.toOpens) n)) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward (chartIso S m hm U).hom).obj
          (AlgebraicGeometry.Proj.twist ((S.veronese m).sectionsGrading U.toOpens) n)) :=
  (AlgebraicGeometry.Scheme.Modules.pushforwardComp ((S.veronese m).toGradedAffineAlgebra.projChart U)
      (leftIso S m hm).hom).app _ ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (projChart_comp_leftIso_hom S m hm U)).app _ ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pushforwardComp (chartIso S m hm U).hom
      (S.toGradedAffineAlgebra.projChart U)).app _).symm

/-- **Step 3a, packaged**: `(e_U.hom)_* O_{Proj A^{(m)}(U)}(n) ≅ ((Proj.veroneseIso A(U) m hm).hom)_* O_{Proj A(U)^{(m)}}(n)`,
from `e_U.hom = Proj.map ofVeronese_U ≫ (Proj.veroneseIso _).hom`, `pushforwardComp`, and the isomorphism
`θ_{ofVeronese} : O(n) ≅ (Proj.map ofVeronese)_* O(n)` of `VeroneseTwistPullbackTwistToPushforwardIso`. -/
def chartTwistPushIsoVeronese (U : X.AffineZariskiSite) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (chartIso S m hm U).hom).obj
        (AlgebraicGeometry.Proj.twist ((S.veronese m).sectionsGrading U.toOpens) n) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).obj
        (AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U.toOpens) m) n) :=
  (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (chartIso_hom S m hm U)).app _ ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pushforwardComp
      (AlgebraicGeometry.Proj.map (ofVeronese S m hm U.toOpens) (irrelevant_le_map_ofVeronese S m hm U.toOpens))
      (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).app _).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).mapIso
      (twistPushforwardOfVeroneseIso S m hm U.toOpens n)

/-- The component at `U` of the diagram isomorphism, given the degree-rescaling isomorphisms `Ψ`:
`(ψ.hom)_* (c'_U)_* O(1) ≅ (c_U)_* (e_U.hom)_* O(1) ≅ (c_U)_* ((Proj.veroneseIso).hom)_* O_{A(U)^{(m)}}(1) ≅ (c_U)_* O_{A(U)}(m)`. -/
def twistDiagramComponentIso
    (Ψ : ∀ U : X.AffineZariskiSite,
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).obj
        (AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U.toOpens) m) 1) ≅
      AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ))
    (U : X.AffineZariskiSite) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso S m hm).hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward ((S.veronese m).toGradedAffineAlgebra.projChart U)).obj
          (AlgebraicGeometry.Proj.twist ((S.veronese m).sectionsGrading U.toOpens) 1)) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).obj
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ)) :=
  twistChartPushIso S m hm U 1 ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).mapIso
      (chartTwistPushIsoVeronese S m hm U 1 ≪≫ Ψ U)

/-- The degree-rescaling isomorphism on the chart `U`, in the form produced by
`Proj.veroneseTwistHom` (`VeroneseTwistPullbackVeroneseComparison`) for `φ := veroneseHom A(U) m`,
`ψ := (Proj.veroneseIso A(U) m hm).hom`, degrees `1 ↦ m`; its hypotheses are `veroneseIso_hom_base_veroneseHom_base`
(`ψ ∘ φ = id` on points), `veroneseHom_isVeroneseContraction` (points) and
`veroneseIso_hom_isVeroneseSectionCompatible` (sections), all from
`VeroneseTwistPullbackVeroneseHomApp`. Pointwise: `s ↦ (𝔭 ↦ (B(U)_{𝔭 ∩ B(U)} → A(U)_𝔭)(s (veroneseHom 𝔭)))`
(`Proj.veroneseTwistHom_app_apply`). -/
abbrev chartTwistHom (U : X.AffineZariskiSite) :
    (AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).obj
      (AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U.toOpens) m) 1) ⟶
    AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ) :=
  AlgebraicGeometry.Proj.veroneseTwistHom
    (AlgebraicGeometry.Proj.veroneseIso_hom_base_veroneseHom_base (S.sectionsGrading U.toOpens) m hm)
    (AlgebraicGeometry.Proj.veroneseHom_isVeroneseContraction (S.sectionsGrading U.toOpens) m hm)
    (AlgebraicGeometry.Proj.veroneseIso_hom_isVeroneseSectionCompatible (S.sectionsGrading U.toOpens) m hm)
    1 (m : ℤ) (one_mul _).symm

end AlgebraicGeometry.Scheme.relativeProj.veroneseIso

end
