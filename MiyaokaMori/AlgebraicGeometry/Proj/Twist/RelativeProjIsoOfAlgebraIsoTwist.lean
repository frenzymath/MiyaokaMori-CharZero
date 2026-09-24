import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIsoGlue
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjIsoOfAlgebraIsoTwistPostcomp

/-! # Isomorphic graded algebras have isomorphic twisting sheaves

Let `φ : S ≅ T` and `e := leftIso φ : Proj_X S ≅ Proj_X T` (step 3). This module

* proves that, chart by chart, the twisting sheaves correspond: the Stacks 01MX comparison map
  `T(invHom φ U) : (ι_U^T)_* O_{Proj A_T(U)}(d) ⟶ (ι_U^S ≫ e)_* O_{Proj A_S(U)}(d)`
  (`Proj.twistPushTransition` along the graded ring isomorphism `invHom φ U : A_T(U) ≅ A_S(U)`) is
  an isomorphism, with inverse `T(toHom φ U)` — by the transitivity and unit laws of
  `twistPushTransition` (`twistChartTransition_comp_inv`, `twistChartTransitionInv_comp`,
  packaged as `twistChartTransition_isIso`);
* proves that these chart isomorphisms are natural in `U` (`twistCompare_naturality`, via the
  transitivity of `twistPushTransition` and its compatibility with post-composition of the charts,
  `twistPushTransition_postcomp` from `RelativeProjIsoOfAlgebraIsoTwistPostcomp`), so that they form
  a natural isomorphism `T.twistDiagram d ≅ S.twistDiagram d ⋙ e_*` (`twistCompareNatIso_exists`);
* passes to the limit (`e_*` is a right adjoint, `preservesLimitIso`; `HasLimit.isoOfNatIso`):
  `O_{Proj_X T}(d) ≅ e_* O_{Proj_X S}(d)` (`twistPushforwardIso_exists`), and transposes along the
  isomorphism `e` (the counit `e^* e_* M ⟶ M` is an isomorphism because `e_*` is fully faithful):
  `O_{Proj_X S}(d) ≅ e^* O_{Proj_X T}(d)`, the global result
  `relativeProj.twist_iso_of_algebra_iso`.

Compile-time notes (why there is no `def` for the comparison maps and why every statement about a
diagram morphism is spelled `(twistDiagram d).map f`) are in the section header "Step 2" below.

Source: Stacks 01MX (θ), 01NP (transitivity of θ), 01LI (gluing of sheaves).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

-- `Proj.twist` is a huge term (sheafified predicate on homogeneous localizations); nothing here
-- needs to look inside it (same guard as in `RelativeProjTwistLimit`).
attribute [local irreducible] AlgebraicGeometry.Proj.twist

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso

attribute [local instance] AlgebraicGeometry.Scheme.GradedAffineAlgebra.hasColimit_projFunctor

variable {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ≅ T)
  (U : X.AffineZariskiSite)

/-- `Proj.map (invHom φ U) ≫ ι_U^T = ι_U^S ≫ e` (chart compatibility of `e`, rewritten). -/
theorem map_invHom_projChart :
    AlgebraicGeometry.Proj.map (invHom φ U) (irrelevant_le_map_invHom φ U) ≫
        T.toGradedAffineAlgebra.projChart U =
      S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom :=
  (projChart_leftIso_hom φ U).symm

/-- `Proj.map (toHom φ U) ≫ (ι_U^S ≫ e) = ι_U^T`. -/
theorem map_toHom_projChart :
    AlgebraicGeometry.Proj.map (toHom φ U) (irrelevant_le_map_toHom φ U) ≫
        (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom) =
      T.toGradedAffineAlgebra.projChart U := by
  rw [projChart_leftIso_hom]
  change (chartIso φ U).inv ≫ (chartIso φ U).hom ≫ T.toGradedAffineAlgebra.projChart U = _
  rw [Iso.inv_hom_id_assoc]

variable (d : ℤ)

theorem toHom_comp_invHom_ringHom :
    ((GradedRingHom.id (T.toGradedAffineAlgebra.grading U) :
        T.toGradedAffineAlgebra.grading U →+*ᵍ T.toGradedAffineAlgebra.grading U) :
      T.toGradedAffineAlgebra.toAffineAlgebra.sections U →+*
        T.toGradedAffineAlgebra.toAffineAlgebra.sections U)
      = ((toHom φ U : S.toGradedAffineAlgebra.toAffineAlgebra.sections U →+*
            T.toGradedAffineAlgebra.toAffineAlgebra.sections U).comp
          (invHom φ U : T.toGradedAffineAlgebra.toAffineAlgebra.sections U →+*
            S.toGradedAffineAlgebra.toAffineAlgebra.sections U)) :=
  RingHom.ext fun x => (toHom_invHom φ U x).symm

theorem invHom_comp_toHom_ringHom :
    ((GradedRingHom.id (S.toGradedAffineAlgebra.grading U) :
        S.toGradedAffineAlgebra.grading U →+*ᵍ S.toGradedAffineAlgebra.grading U) :
      S.toGradedAffineAlgebra.toAffineAlgebra.sections U →+*
        S.toGradedAffineAlgebra.toAffineAlgebra.sections U)
      = ((invHom φ U : T.toGradedAffineAlgebra.toAffineAlgebra.sections U →+*
            S.toGradedAffineAlgebra.toAffineAlgebra.sections U).comp
          (toHom φ U : S.toGradedAffineAlgebra.toAffineAlgebra.sections U →+*
            T.toGradedAffineAlgebra.toAffineAlgebra.sections U)) :=
  RingHom.ext fun x => (invHom_toHom φ U x).symm

theorem map_id_comp_projChart (R : X.GradedQCAlgebra) :
    AlgebraicGeometry.Proj.map (GradedRingHom.id (R.toGradedAffineAlgebra.grading U)) (by simp) ≫
        R.toGradedAffineAlgebra.projChart U = R.toGradedAffineAlgebra.projChart U := by
  rw [AlgebraicGeometry.Proj.map_id, Category.id_comp]

theorem map_id_comp_projChart' :
    AlgebraicGeometry.Proj.map (GradedRingHom.id (S.toGradedAffineAlgebra.grading U)) (by simp) ≫
        (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom) =
      S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom := by
  rw [AlgebraicGeometry.Proj.map_id, Category.id_comp]

/-! The chart-level comparison maps are `Proj.twistPushTransition` along `invHom φ U` (resp.
`toHom φ U`). **They are deliberately not wrapped in a `def`**: with a `def` head under `≫`, the
kernel check of the two-sided-inverse laws below takes > 45 s (the same phenomenon as in
`RelativeProjTwistLimit`); stated directly in `twistPushTransition` terms it takes < 1 s. -/

/-- `T(invHom) ≫ T(toHom) = T(toHom ∘ invHom) = T(id) = 𝟙` (Stacks 01NP transitivity + unit law). -/
theorem twistChartTransition_comp_inv :
    AlgebraicGeometry.Proj.twistPushTransition (invHom φ U) (irrelevant_le_map_invHom φ U) d
      (T.toGradedAffineAlgebra.projChart U) (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
      (map_invHom_projChart φ U) ≫
    AlgebraicGeometry.Proj.twistPushTransition (toHom φ U) (irrelevant_le_map_toHom φ U) d
      (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom) (T.toGradedAffineAlgebra.projChart U)
      (map_toHom_projChart φ U) = 𝟙 _ := by
  have h := AlgebraicGeometry.Proj.twistPushTransition_comp (invHom φ U) (toHom φ U)
    (GradedRingHom.id (T.toGradedAffineAlgebra.grading U))
    (irrelevant_le_map_invHom φ U) (irrelevant_le_map_toHom φ U) (by simp) d
    (toHom_comp_invHom_ringHom φ U)
    (T.toGradedAffineAlgebra.projChart U) (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
    (T.toGradedAffineAlgebra.projChart U)
    (map_invHom_projChart φ U) (map_toHom_projChart φ U) (map_id_comp_projChart U T)
  exact h.symm.trans (AlgebraicGeometry.Proj.twistPushTransition_id _ _ d rfl _ _)

/-- `T(toHom) ≫ T(invHom) = 𝟙`. -/
theorem twistChartTransitionInv_comp :
    AlgebraicGeometry.Proj.twistPushTransition (toHom φ U) (irrelevant_le_map_toHom φ U) d
      (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom) (T.toGradedAffineAlgebra.projChart U)
      (map_toHom_projChart φ U) ≫
    AlgebraicGeometry.Proj.twistPushTransition (invHom φ U) (irrelevant_le_map_invHom φ U) d
      (T.toGradedAffineAlgebra.projChart U) (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
      (map_invHom_projChart φ U) = 𝟙 _ := by
  have h := AlgebraicGeometry.Proj.twistPushTransition_comp (toHom φ U) (invHom φ U)
    (GradedRingHom.id (S.toGradedAffineAlgebra.grading U))
    (irrelevant_le_map_toHom φ U) (irrelevant_le_map_invHom φ U) (by simp) d
    (invHom_comp_toHom_ringHom φ U)
    (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom) (T.toGradedAffineAlgebra.projChart U)
    (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
    (map_toHom_projChart φ U) (map_invHom_projChart φ U) (map_id_comp_projChart' φ U)
  exact h.symm.trans (AlgebraicGeometry.Proj.twistPushTransition_id _ _ d rfl _ _)

/-- The chart-level comparison map is an isomorphism:
`(ι_U^T)_* O_{Proj A_T(U)}(d) ≅ (ι_U^S ≫ e)_* O_{Proj A_S(U)}(d)` (inverse: the comparison map along
`toHom φ U`). Stated as `IsIso` (a `theorem`), not as a `def`-packaged `Iso`: a `def` whose body
contains these two proofs is kernel-checked in > 45 s (nested-proof abstraction, cf.
`RelativeProjTwistLimit`); the `theorem` is checked in < 1 s. Use `asIso` downstream. -/
theorem twistChartTransition_isIso :
    IsIso (AlgebraicGeometry.Proj.twistPushTransition (invHom φ U) (irrelevant_le_map_invHom φ U) d
      (T.toGradedAffineAlgebra.projChart U) (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
      (map_invHom_projChart φ U)) :=
  ⟨⟨AlgebraicGeometry.Proj.twistPushTransition (toHom φ U) (irrelevant_le_map_toHom φ U) d
    (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom) (T.toGradedAffineAlgebra.projChart U)
    (map_toHom_projChart φ U), twistChartTransition_comp_inv φ U d, twistChartTransitionInv_comp φ U d⟩⟩

end AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- `map_projChart` with the chart transition written as `Proj.map` (the form `twistTransition` uses). -/
theorem map_restrictGraded_projChart {U V : X.AffineZariskiSite} (h : U ≤ V) :
    AlgebraicGeometry.Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) ≫ S.projChart V =
      S.projChart U :=
  S.map_projChart h

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso

variable {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ≅ T)

theorem irrelevant_le_map_invHom_comp_restrict {U V : X.AffineZariskiSite} (h : U ≤ V) :
    HomogeneousIdeal.irrelevant (S.toGradedAffineAlgebra.grading U) ≤
      (HomogeneousIdeal.irrelevant (T.toGradedAffineAlgebra.grading V)).map
        ((invHom φ U).comp (T.toGradedAffineAlgebra.restrictGraded h)) :=
  HomogeneousIdeal.irrelevant_le_map_comp (T.toGradedAffineAlgebra.restrict_irrelevant_le h)
    (irrelevant_le_map_invHom φ U)

theorem irrelevant_le_map_restrict_comp_invHom {U V : X.AffineZariskiSite} (h : U ≤ V) :
    HomogeneousIdeal.irrelevant (S.toGradedAffineAlgebra.grading U) ≤
      (HomogeneousIdeal.irrelevant (T.toGradedAffineAlgebra.grading V)).map
        ((S.toGradedAffineAlgebra.restrictGraded h).comp (invHom φ V)) :=
  HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_invHom φ V)
    (S.toGradedAffineAlgebra.restrict_irrelevant_le h)

theorem map_invHom_comp_restrict_projChart {U V : X.AffineZariskiSite} (h : U ≤ V) :
    AlgebraicGeometry.Proj.map ((invHom φ U).comp (T.toGradedAffineAlgebra.restrictGraded h))
        (irrelevant_le_map_invHom_comp_restrict φ h) ≫ T.toGradedAffineAlgebra.projChart V =
      S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom := by
  rw [AlgebraicGeometry.Proj.map_comp (T.toGradedAffineAlgebra.restrictGraded h) (invHom φ U)
    (T.toGradedAffineAlgebra.restrict_irrelevant_le h) (irrelevant_le_map_invHom φ U), Category.assoc,
    T.toGradedAffineAlgebra.map_restrictGraded_projChart h, map_invHom_projChart]

theorem map_restrict_comp_invHom_projChart {U V : X.AffineZariskiSite} (h : U ≤ V) :
    AlgebraicGeometry.Proj.map ((S.toGradedAffineAlgebra.restrictGraded h).comp (invHom φ V))
        (irrelevant_le_map_restrict_comp_invHom φ h) ≫ T.toGradedAffineAlgebra.projChart V =
      S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom := by
  rw [AlgebraicGeometry.Proj.map_comp (invHom φ V) (S.toGradedAffineAlgebra.restrictGraded h)
    (irrelevant_le_map_invHom φ V) (S.toGradedAffineAlgebra.restrict_irrelevant_le h), Category.assoc,
    map_invHom_projChart, ← Category.assoc, S.toGradedAffineAlgebra.map_restrictGraded_projChart h]

theorem map_restrictGraded_projChart_leftIso {U V : X.AffineZariskiSite} (h : U ≤ V) :
    AlgebraicGeometry.Proj.map (S.toGradedAffineAlgebra.restrictGraded h)
        (S.toGradedAffineAlgebra.restrict_irrelevant_le h) ≫
        (S.toGradedAffineAlgebra.projChart V ≫ (leftIso φ).hom) =
      S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom := by
  rw [← Category.assoc, S.toGradedAffineAlgebra.map_restrictGraded_projChart h]

variable (d : ℤ)

/-! ### Step 2: naturality of the chart comparisons in `U`

For `U ≤ V` write `τ_U` for the comparison map `T(invHom φ U)` of step 1 followed by the inverse of
`pushforwardComp`, i.e. `(ι_U^T)_* O_T(U)(d) ⟶ e_* (ι_U^S)_* O_S(U)(d)`. The square
`T.twistTransition d h ≫ τ_U = τ_V ≫ e_*(S.twistTransition d h)` commutes:
both sides are `T(χ)` for the graded ring homomorphism `χ = invHom φ U ∘ res_T = res_S ∘ invHom φ V :
A_T(V) → A_S(U)` (`restrictGraded_comp_invHom`), by the transitivity `twistPushTransition_comp`
(twice) and the post-composition formula `twistPushTransition_postcomp` for `e`.

**Compile-time design.** The kernel compares two composite morphisms of
sheaves of modules by unfolding `≫` (an `abbrev`-headed projection) down to sections; if the two
spellings differ *anywhere* below `≫` — even by a proof term, e.g. the `_proof_i` constants that
nested-proof abstraction inserts into the body of every `def` — this costs 35–45 s (it unfolds
`Proj.twist`, which the kernel does not treat as irreducible). Hence in this file:
* no `def` wraps a morphism of sheaves (`twistCompareHom`-style definitions were measured at 38 s
  for the single check `IsIso (twistCompareHom …)`); the components are written out;
* every statement about a diagram morphism spells it as `(twistDiagram d).map f`, never as the
  definitionally equal raw `twistPushTransition` (an `HEq` between the two under `pushforward.map`
  was measured at 44 s); the raw form is used only inside proofs, via equations proved by `rfl`
  that the kernel checks at the top level (`Functor.map` vs. a regular constant: milliseconds);
* the natural isomorphism and the final isomorphism are built inside `theorem`s (`Nonempty …`),
  where no nested-proof abstraction happens, and the naturality field is filled through the bridge
  lemma `comp₂_eq_comp₂_of_heq_bridge`. -/

/-- Naturality of the chart comparisons, raw form (`U ≤ V`, all maps spelled as `twistPushTransition`). -/
theorem twistCompare_naturality_raw {U V : X.AffineZariskiSite} (h : U ≤ V) :
    (AlgebraicGeometry.Proj.twistPushTransition (T.toGradedAffineAlgebra.restrictGraded h)
        (T.toGradedAffineAlgebra.restrict_irrelevant_le h) d (T.toGradedAffineAlgebra.projChart V)
        (T.toGradedAffineAlgebra.projChart U) (T.toGradedAffineAlgebra.map_projChart h)) ≫
      (AlgebraicGeometry.Proj.twistPushTransition (invHom φ U) (irrelevant_le_map_invHom φ U) d
        (T.toGradedAffineAlgebra.projChart U) (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
        (map_invHom_projChart φ U) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (S.toGradedAffineAlgebra.projChart U)
        (leftIso φ).hom).inv.app (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U) d)) =
    (AlgebraicGeometry.Proj.twistPushTransition (invHom φ V) (irrelevant_le_map_invHom φ V) d
        (T.toGradedAffineAlgebra.projChart V) (S.toGradedAffineAlgebra.projChart V ≫ (leftIso φ).hom)
        (map_invHom_projChart φ V) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (S.toGradedAffineAlgebra.projChart V)
        (leftIso φ).hom).inv.app (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading V) d)) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso φ).hom).map
        (AlgebraicGeometry.Proj.twistPushTransition (S.toGradedAffineAlgebra.restrictGraded h)
        (S.toGradedAffineAlgebra.restrict_irrelevant_le h) d (S.toGradedAffineAlgebra.projChart V)
        (S.toGradedAffineAlgebra.projChart U) (S.toGradedAffineAlgebra.map_projChart h)) := by
  have R1 := AlgebraicGeometry.Proj.twistPushTransition_comp
    (T.toGradedAffineAlgebra.restrictGraded h) (invHom φ U)
    ((invHom φ U).comp (T.toGradedAffineAlgebra.restrictGraded h))
    (T.toGradedAffineAlgebra.restrict_irrelevant_le h) (irrelevant_le_map_invHom φ U)
    (irrelevant_le_map_invHom_comp_restrict φ h) d rfl
    (T.toGradedAffineAlgebra.projChart V) (T.toGradedAffineAlgebra.projChart U)
    (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
    (T.toGradedAffineAlgebra.map_projChart h) (map_invHom_projChart φ U)
    (map_invHom_comp_restrict_projChart φ h)
  have R2 := AlgebraicGeometry.Proj.twistPushTransition_comp
    (invHom φ V) (S.toGradedAffineAlgebra.restrictGraded h)
    ((S.toGradedAffineAlgebra.restrictGraded h).comp (invHom φ V))
    (irrelevant_le_map_invHom φ V) (S.toGradedAffineAlgebra.restrict_irrelevant_le h)
    (irrelevant_le_map_restrict_comp_invHom φ h) d rfl
    (T.toGradedAffineAlgebra.projChart V) (S.toGradedAffineAlgebra.projChart V ≫ (leftIso φ).hom)
    (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
    (map_invHom_projChart φ V) (map_restrictGraded_projChart_leftIso φ h)
    (map_restrict_comp_invHom_projChart φ h)
  have R3 := AlgebraicGeometry.Proj.twistPushTransition_congr (restrictGraded_comp_invHom φ h)
    (irrelevant_le_map_restrict_comp_invHom φ h) (irrelevant_le_map_invHom_comp_restrict φ h) d
    (T.toGradedAffineAlgebra.projChart V) (S.toGradedAffineAlgebra.projChart U ≫ (leftIso φ).hom)
    (map_restrict_comp_invHom_projChart φ h) (map_invHom_comp_restrict_projChart φ h)
  have R4 := AlgebraicGeometry.Proj.twistPushTransition_postcomp
    (S.toGradedAffineAlgebra.restrictGraded h) (S.toGradedAffineAlgebra.restrict_irrelevant_le h) d
    (S.toGradedAffineAlgebra.projChart V) (S.toGradedAffineAlgebra.projChart U)
    (S.toGradedAffineAlgebra.map_projChart h) (leftIso φ).hom
    (map_restrictGraded_projChart_leftIso φ h)
  rw [← Category.assoc, ← R1, Category.assoc,
    ← cancel_mono ((AlgebraicGeometry.Scheme.Modules.pushforwardComp
      (S.toGradedAffineAlgebra.projChart U) (leftIso φ).hom).hom.app
        (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U) d)),
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Category.assoc, Category.assoc, ← R4, ← R2, R3]

/-- Naturality of the chart comparisons, in terms of `twistDiagram` (the spelling that
`NatIso.ofComponents` needs). -/
theorem twistCompare_naturality {U V : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V) :
    (T.toGradedAffineAlgebra.twistDiagram d).map f ≫
      (AlgebraicGeometry.Proj.twistPushTransition (invHom φ V.unop) (irrelevant_le_map_invHom φ V.unop) d
        (T.toGradedAffineAlgebra.projChart V.unop) (S.toGradedAffineAlgebra.projChart V.unop ≫ (leftIso φ).hom)
        (map_invHom_projChart φ V.unop) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (S.toGradedAffineAlgebra.projChart V.unop)
        (leftIso φ).hom).inv.app (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading V.unop) d)) =
    (AlgebraicGeometry.Proj.twistPushTransition (invHom φ U.unop) (irrelevant_le_map_invHom φ U.unop) d
        (T.toGradedAffineAlgebra.projChart U.unop) (S.toGradedAffineAlgebra.projChart U.unop ≫ (leftIso φ).hom)
        (map_invHom_projChart φ U.unop) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (S.toGradedAffineAlgebra.projChart U.unop)
        (leftIso φ).hom).inv.app (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U.unop) d)) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso φ).hom).map
        ((S.toGradedAffineAlgebra.twistDiagram d).map f) := by
  have hT : (T.toGradedAffineAlgebra.twistDiagram d).map f =
      AlgebraicGeometry.Proj.twistPushTransition
        (T.toGradedAffineAlgebra.restrictGraded (leOfHom f.unop))
        (T.toGradedAffineAlgebra.restrict_irrelevant_le (leOfHom f.unop)) d
        (T.toGradedAffineAlgebra.projChart U.unop) (T.toGradedAffineAlgebra.projChart V.unop)
        (T.toGradedAffineAlgebra.map_projChart (leOfHom f.unop)) := rfl
  have hS : (S.toGradedAffineAlgebra.twistDiagram d).map f =
      AlgebraicGeometry.Proj.twistPushTransition
        (S.toGradedAffineAlgebra.restrictGraded (leOfHom f.unop))
        (S.toGradedAffineAlgebra.restrict_irrelevant_le (leOfHom f.unop)) d
        (S.toGradedAffineAlgebra.projChart U.unop) (S.toGradedAffineAlgebra.projChart V.unop)
        (S.toGradedAffineAlgebra.map_projChart (leOfHom f.unop)) := rfl
  rw [hT, hS]
  exact twistCompare_naturality_raw φ d (leOfHom f.unop)

/-! ### Steps 3–5: the natural isomorphism of diagrams, the limit, the transpose -/

/-- **Step 3.** `T.twistDiagram d ≅ S.twistDiagram d ⋙ e_*`, with components `τ_U`
(isomorphisms by `twistChartTransition_isIso`) and naturality `twistCompare_naturality`. -/
theorem twistCompareNatIso_exists :
    Nonempty (T.toGradedAffineAlgebra.twistDiagram d ≅
      S.toGradedAffineAlgebra.twistDiagram d ⋙
        AlgebraicGeometry.Scheme.Modules.pushforward (leftIso φ).hom) :=
  ⟨NatIso.ofComponents
    (fun U =>
      haveI := twistChartTransition_isIso φ U.unop d
      -- the type ascription makes the objects of this `≫` the raw pushforwards (not
      -- `(twistDiagram d).obj U`), so that the kernel matches it against `twistCompare_naturality`
      (asIso (AlgebraicGeometry.Proj.twistPushTransition (invHom φ U.unop) (irrelevant_le_map_invHom φ U.unop) d
        (T.toGradedAffineAlgebra.projChart U.unop) (S.toGradedAffineAlgebra.projChart U.unop ≫ (leftIso φ).hom)
        (map_invHom_projChart φ U.unop) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (S.toGradedAffineAlgebra.projChart U.unop)
        (leftIso φ).hom).inv.app (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U.unop) d)) :
        (AlgebraicGeometry.Scheme.Modules.pushforward (T.toGradedAffineAlgebra.projChart U.unop)).obj
            (AlgebraicGeometry.Proj.twist (T.toGradedAffineAlgebra.grading U.unop) d) ≅
          (AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U.unop) ⋙
            AlgebraicGeometry.Scheme.Modules.pushforward (leftIso φ).hom).obj
            (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading U.unop) d)))
    (fun f => CategoryTheory.comp₂_eq_comp₂_of_heq_bridge (twistCompare_naturality φ d f) _ _ _ _
      rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)⟩

/-- **Step 4.** `O_T(d) ≅ e_* O_S(d)`: `e_*` is a right adjoint, so it preserves the limit defining
`O_S(d)` (`preservesLimitIso`), and `HasLimit.isoOfNatIso` transports along step 3. -/
theorem twistPushforwardIso_exists :
    Nonempty (T.toGradedAffineAlgebra.twist d ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso φ).hom).obj
        (S.toGradedAffineAlgebra.twist d)) :=
  haveI : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ
      S.toGradedAffineAlgebra.relativeProj.left.Modules := SheafOfModules.hasLimitsOfShape _ _
  haveI : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ
      T.toGradedAffineAlgebra.relativeProj.left.Modules := SheafOfModules.hasLimitsOfShape _ _
  (twistCompareNatIso_exists φ d).elim fun η =>
  ⟨eqToIso (T.toGradedAffineAlgebra.twist_eq_limit d) ≪≫
    HasLimit.isoOfNatIso η ≪≫
    (preservesLimitIso (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso φ).hom)
      (S.toGradedAffineAlgebra.twistDiagram d)).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso φ).hom).mapIso
      (eqToIso (S.toGradedAffineAlgebra.twist_eq_limit d)).symm⟩

/-- **Step 5, the input.** `e` is an isomorphism, hence an open immersion (`IsOpenImmersion.of_isIso`),
so `e_*` is fully faithful (Mathlib's instances for `Scheme.Modules.pushforward`) and the counit
`e^* e_* M ⟶ M` of `pullbackPushforwardAdjunction e` is an isomorphism
(`Adjunction.counit_isIso_of_R_fully_faithful`). -/
theorem isIso_counit_app (M : S.toGradedAffineAlgebra.relativeProj.left.Modules) :
    IsIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (leftIso φ).hom).counit.app M) :=
  inferInstance

/-- **Step 5.** `O_S(d) ≅ e^* O_T(d)`: apply `e^*` to step 4 and compose with the counit at `O_S(d)`. -/
theorem twist_iso_of_algebra_iso' :
    Nonempty (S.toGradedAffineAlgebra.twist d ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (leftIso φ).hom).obj
        (T.toGradedAffineAlgebra.twist d)) :=
  haveI := isIso_counit_app φ (S.toGradedAffineAlgebra.twist d)
  (twistPushforwardIso_exists φ d).elim fun i =>
  ⟨((AlgebraicGeometry.Scheme.Modules.pullback (leftIso φ).hom).mapIso i ≪≫
    asIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (leftIso φ).hom).counit.app
      (S.toGradedAffineAlgebra.twist d))).symm⟩

end AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso

/-- **The twisting sheaves under an isomorphism of graded algebras** (the third clause of
the isomorphism of relative Proj induced by an isomorphism of graded algebras): for `φ : S ≅ T` and `e := projIsoOfIso.leftIso φ`,
`O_{Proj_X S}(d) ≅ e^* O_{Proj_X T}(d)`.

Source: Stacks 01NP (functoriality of relative Proj and of its twists; the θ of 01MX is an
isomorphism along an isomorphism of graded rings), 01LI (gluing of sheaves along a locally directed
cover). The paper uses this silently whenever it identifies `Proj_C S` with `Proj_C S'` for
isomorphic graded algebras (e.g. in the deformation to the split case).

**Proof (the steps below name the Lean declarations).** Write `e = leftIso φ`,
`ι_U^S := S.projChart U`, `ι_U^T := T.projChart U` for `U` in the small affine Zariski site, and
`O_S(d) := twist S d = lim_U (ι_U^S)_* O_{Proj A_S(U)}(d)` (`GradedAffineAlgebra.twist_eq_limit`,
diagram `twistDiagram d` with transition maps `twistTransition` = `Proj.twistPushTransition` along the
restriction `A_S(V) → A_S(U)`), and likewise for `T`.

1. *Chart level (already proved above).* `ι_U^S ≫ e = Proj.map (invHom φ U) ≫ ι_U^T`
   (`projChart_leftIso_hom`), so `Proj.twistPushTransition` along the graded ring isomorphism
   `invHom φ U : A_T(U) → A_S(U)` gives `τ_U : (ι_U^T)_* O_T(U)(d) ⟶ (ι_U^S ≫ e)_* O_S(U)(d)`,
   an isomorphism with inverse the transition along `toHom φ U` (`twistChartTransition_isIso`: transitivity
   `twistPushTransition_comp` and unit law `twistPushTransition_id`).
2. *Naturality in `U`.* For `U ≤ V` (i.e. `U = D_V(f)`), the square
   `T.twistTransition d h ≫ τ_U = τ_V ≫ τ'_{U≤V}` commutes, where `τ'_{U≤V}` is
   `Proj.twistPushTransition` along `S.restrictGraded h` with the charts `ι^S ≫ e`
   (both sides are the transition along the same ring homomorphism
   `A_T(V) → A_S(U)`, namely `invHom φ U ∘ T.restrictGraded h = S.restrictGraded h ∘ invHom φ V`
   — `restrictGraded_comp_invHom` — by `twistPushTransition_comp` used twice).
   Hence `U ↦ τ_U` is a natural isomorphism from `T.twistDiagram d` to the diagram
   `D'_S : U ↦ (ι_U^S ≫ e)_* O_S(U)(d)` with transitions `τ'`.
3. *Identify `D'_S` with `e_* ∘ S.twistDiagram d`.* `(ι_U^S ≫ e)_* = e_* ∘ (ι_U^S)_*`
   (`Modules.pushforwardComp`), and `τ'_{U≤V} = e_*(S.twistTransition d h)` under this
   identification: unfold `twistPushTransition` (it is `(ι_V)_*(θ) ≫ pushforwardComp ≫
   pushforwardCongr`) and use the coherence of `pushforwardComp` with composition and
   `pushforwardCongr` (all of these are identities on sections: `pushforwardComp_hom_app_app`,
   `pushforwardCongr_hom_app_app`; compare the proof of `twistPushTransition_app_apply`, where the
   whole map is computed pointwise as `s ↦ (y ↦ localRingHom (s (comap y)))`). So
   `D'_S ≅ S.twistDiagram d ⋙ Modules.pushforward e.hom`.
4. *Pass to the limit.* `Modules.pushforward e.hom` is a right adjoint
   (`pullbackPushforwardAdjunction`), hence preserves limits (`preservesLimitIso`):
   `e_* O_S(d) = e_*(lim S.twistDiagram d) ≅ lim (S.twistDiagram d ⋙ e_*) ≅ lim D'_S ≅
   lim T.twistDiagram d = O_T(d)` (`HasLimit.isoOfNatIso` for the last two steps, with the natural
   isomorphisms of 2 and 3). This gives `O_T(d) ≅ e_* O_S(d)`.
5. *Transpose along the isomorphism `e`.* `Modules.pushforward e.hom` is an equivalence
   (quasi-inverse `pushforward e.inv`, via `pushforwardComp` and `pushforwardId`), so its left
   adjoint `pullback e.hom` is a quasi-inverse too: the counit `e^* e_* M ⟶ M` of
   `pullbackPushforwardAdjunction e.hom` is an isomorphism for every `M`
   (`Functor.isEquivalence_of_isRightAdjoint` / `Adjunction.isIso_counit_of_isEquivalence`, or
   directly: `pullback e.hom ≅ pushforward e.inv` by uniqueness of left adjoints
   `Adjunction.leftAdjointUniq`, and `pushforward e.inv (pushforward e.hom M) ≅ M`). Applying
   `pullback e.hom` to the isomorphism of step 4 and composing with the counit at `O_S(d)` gives
   `e^* O_T(d) ≅ e^* e_* O_S(d) ≅ O_S(d)`.

Where the steps live: step 1 `twistChartTransition_isIso`; step 2 `twistCompare_naturality_raw`
(the square, via `twistPushTransition_comp` twice, `twistPushTransition_congr` along
`restrictGraded_comp_invHom`, and `twistPushTransition_postcomp`) and `twistCompare_naturality`;
steps 2–3 together give `twistCompareNatIso_exists` (the diagram `D'_S` is never formed: the
components `τ_U ≫ pushforwardComp⁻¹` land directly in `S.twistDiagram d ⋙ e_*`); step 4
`twistPushforwardIso_exists`; step 5 `isIso_counit_app` (Mathlib: `IsOpenImmersion.of_isIso`,
`Scheme.Modules.pushforward` fully faithful along open immersions,
`Adjunction.counit_isIso_of_R_fully_faithful`) and `twist_iso_of_algebra_iso'`.

Edge cases: `X = ∅` (empty site, both twists are the terminal module, `e` is the identity of the
empty scheme); `d` arbitrary in `ℤ` (nothing depends on the sign); `S = T`, `φ = 𝟙`
(`e = 𝟙` by `Proj.map_id`, all τ are identities). Statement re-checked: it is exactly the third
clause of the locked target statement with `e := leftIso φ`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twist_iso_of_algebra_iso
    {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ≅ T) (d : ℤ) :
    Nonempty (AlgebraicGeometry.Scheme.relativeProj.twist S d ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso.leftIso φ).hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist T d)) :=
  AlgebraicGeometry.Scheme.GradedQCAlgebra.projIsoOfIso.twist_iso_of_algebra_iso' φ d

end
