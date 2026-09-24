import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistChartIso

/-! # The twisting sheaf of a relative Proj on an affine open (Stacks 01NR)

Stacks 01NR: on an affine open `U`, the twisting sheaf of the relative Proj is the twisting
sheaf `O(n)` of `Proj(S(U))`, compatibly with the isomorphism `π⁻¹U ≅ Proj S(U)` of Stacks 01NQ
(and the multiplication maps `O(n) ⊗ O(m) → O(n+m)` correspond chart by chart).

The comparison map `c_U^* O(n) ⟶ O_U(n)` is `GradedAffineAlgebra.twistChartHom`, and the
compatibility `e.hom ≫ c = ι` is `affineIso_inv_ι` (Stacks 01NQ). The only remaining
obligation is that the restriction of the glued sheaf to a chart is that chart (Stacks 01LI):
`isIso_twistAffineHom` follows from `GradedAffineAlgebra.isIso_twistChartHom`
(module `RelativeProjTwistChartIso`), since the three other factors of `twistAffineHom` are
components of natural isomorphisms and `pullback e.hom` preserves isomorphisms.

See Lemma 2.2 of the paper for the role of `O(m)` on the relative Proj.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Construction (the comparison map at `U` of the gluing of Stacks 01LI): `twistChartHom` gives
   `c_U^* O(n) ⟶ O_U(n)` (with `c_U := projChart U`); the open immersion `ι` of `π⁻¹(U)` equals
   `affineIso.hom ≫ c_U` (`affineIso_inv_ι`), hence
   `O(n)|_{π⁻¹U} ≅ ι^* O(n)` (`restrictFunctorIsoPullback`) `≅ (e ≫ c_U)^* O(n) ≅ e^* c_U^* O(n) → e^* O_U(n)`.
   That this is an isomorphism (the restriction of the glued sheaf to a chart is that chart,
   Stacks 01LI) is the proof obligation; the inverse is taken with `asIso`. -/

/-- The comparison map `O(n)|_{π⁻¹U} ⟶ e^* O_U(n)` (the underlying morphism of `twistAffineIso`,
stated separately so that one can assert it is an isomorphism). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistAffineHom {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S n).restrict
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom).obj
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n) :=
  let ι := ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι
  let e := AlgebraicGeometry.Scheme.relativeProj.affineIso S U
  let c : AlgebraicGeometry.Proj (S.sectionsGrading U.1) ⟶
      (AlgebraicGeometry.Scheme.relativeProj S).left :=
    S.toGradedAffineAlgebra.projChart ⟨U.1, U.2⟩
  let T := AlgebraicGeometry.Scheme.relativeProj.twist S n
  have hc : e.hom ≫ c = ι := by
    have h : e.inv ≫ ι = c := AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S U
    rw [← h, ← CategoryTheory.Category.assoc, e.hom_inv_id, CategoryTheory.Category.id_comp]
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).hom.app T ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hc.symm).hom.app T ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom c).inv.app T ≫
    (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map (S.toGradedAffineAlgebra.twistChartHom n ⟨U.1, U.2⟩)

/-- Stacks 01LI: the restriction of the glued sheaf to a chart is that chart. Mathematically,
`twistπ` is a limit projection and the transition maps `twistTransition` between charts are
isomorphisms (`θ_f` is `O_V(m)|_U ≅ O_U(m)` for `U ≤ V`, Stacks 01MM), so on the image of `ι_U`
the limit is computed by the `U`-th term.

Proof: `twistAffineHom` is `iso ≫ iso ≫ iso ≫ (pullback e.hom).map (twistChartHom n U)`, and
`twistChartHom n U` is an isomorphism by `GradedAffineAlgebra.isIso_twistChartHom`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.isIso_twistAffineHom {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U n) := by
  -- Instance search cannot see that `Proj (S.sectionsGrading U.1)` and `Proj (S.grading ⟨U.1, U.2⟩)` are the
  -- same scheme (that needs unfolding `sectionsGrading`), so the last two factors get explicit terms.
  have h := S.toGradedAffineAlgebra.isIso_twistChartHom n ⟨U.1, U.2⟩
  unfold AlgebraicGeometry.Scheme.relativeProj.twistAffineHom
  dsimp only
  exact CategoryTheory.IsIso.comp_isIso' inferInstance (CategoryTheory.IsIso.comp_isIso' inferInstance
    (CategoryTheory.IsIso.comp_isIso' (CategoryTheory.NatIso.isIso_app_of_isIso _ _)
      (@CategoryTheory.Functor.map_isIso _ _ _ _ _ _ _ _ h)))

/-- The isomorphism `O(n)|_{π⁻¹U} ≅ e^* O_U(n)` of Stacks 01NR. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistAffineIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) (n : ℤ) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S n).restrict
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).hom).obj
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) n) :=
  haveI := AlgebraicGeometry.Scheme.relativeProj.isIso_twistAffineHom S U n
  CategoryTheory.asIso (AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S U n)

end
