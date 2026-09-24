import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIsoGlue
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjIsoOfAlgebraIsoTwist

/-! # Isomorphic graded algebras have isomorphic relative Proj

Statement: if two graded quasi-coherent algebras `S ≅ T` on `X` are isomorphic, then their relative
Proj are isomorphic over `X`: there is `e : Proj_X S ≅ Proj_X T` with `e ≫ π_T = π_S`, and for every
`d ∈ ℤ` an isomorphism `O_{Proj S}(d) ≅ e^* O_{Proj T}(d)`.

Proof (four steps, in four modules):
1. `RelativeProjIsoOfAlgebraIsoSectionsHom`: for every open `U`, taking sections of `φ : S ⟶ T`
   degreewise gives a graded ring homomorphism `A_S(U) → A_T(U)` (`Hom.sectionsGradedHom`;
   compatibility with multiplication and unit from `Hom.map_mul` (via `tensorHom_tensorSections`) and
   `Hom.map_one`), functorial (`sectionsGradedHom_id/comp`), natural in restriction
   (`sectionsGradedHom_restrict`, the naturality of the sheaf maps `φ.app m`), and compatible with
   the structure maps `Γ(X,U) → A(U)_0` (`sectionsGradedHom_sectionsUnit`).
2. `RelativeProjIsoOfAlgebraIsoChart`: when `φ` is an isomorphism, `toHom φ U` and `invHom φ U` are
   mutually inverse, so the irrelevant-ideal condition of `Proj.map` holds
   (`irrelevant_le_map_of_leftInverse`), and Mathlib's `Proj.map (invHom φ U)` gives
   `Proj A_S(U) ≅ Proj A_T(U)` (`chartIso`; inverse by `Proj.map_comp`, `Proj.map_id`); natural for
   `U ≤ V` (`chartIso_naturality`: both sides are `Proj.map` of the same graded ring map) and
   compatible with the structure morphism to `U` (`chartIso_hom_projToOpen`:
   `AlgebraicGeometry.Proj.proj_map_toSpecZero` + unit compatibility).
3. `RelativeProjIsoOfAlgebraIsoGlue`: `NatIso.ofComponents` gives a natural isomorphism `natIso` of
   the gluing functors; the colimit (`HasColimit.isoOfNatIso`) gives `e = leftIso φ`;
   `colimit.hom_ext` + `projChart_hom` + the compatibility of step 2 give `e ≫ π_T = π_S`
   (`leftIso_hom_comp`). Chart compatibility: `projChart_leftIso_hom`.
4. `RelativeProjIsoOfAlgebraIsoTwist`: chart by chart, the comparison map `Proj.twistPushTransition`
   of Stacks 01MX along the graded ring isomorphism `invHom φ U` is an isomorphism
   `(ι_U^T)_* O_T(U)(d) ≅ (ι_U^S ≫ e)_* O_S(U)(d)` (`twistChartTransition_isIso`, from
   `twistPushTransition_comp/_id`); gluing along the limit of `twistDiagram` gives
   `O_{Proj S}(d) ≅ e^* O_{Proj T}(d)` (`relativeProj.twist_iso_of_algebra_iso`).

Source: functoriality of the relative Proj (Stacks 01NP) and Stacks 01MM. Used for the deformation
to a split weighted bundle in the proof of Proposition 2.4 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso
    {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ≅ T) :
    ∃ e : (AlgebraicGeometry.Scheme.relativeProj S).left ≅
        (AlgebraicGeometry.Scheme.relativeProj T).left,
      e.hom ≫ (AlgebraicGeometry.Scheme.relativeProj T).hom =
        (AlgebraicGeometry.Scheme.relativeProj S).hom ∧
      ∀ d : ℤ, Nonempty (AlgebraicGeometry.Scheme.relativeProj.twist S d ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist T d)) :=
  ⟨AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso.leftIso φ,
    AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso.leftIso_hom_comp' φ,
    fun d => AlgebraicGeometry.Scheme.relativeProj.twist_iso_of_algebra_iso φ d⟩

end
