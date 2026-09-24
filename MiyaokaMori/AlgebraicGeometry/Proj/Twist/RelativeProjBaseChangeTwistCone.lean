import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeGlue
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictTranspose
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLimit
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistPiApp
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLocalIso

/-! # Local comparison maps for the twisting sheaf under base change

Statement: the **local comparison maps** for the twisting sheaf under base change (Stacks 01O3,
second assertion), for a small chart `i = (U, V)` of `Proj_{S'}(g^*𝒜)` (`BaseChangeChartIndex g`).
Write `φ = baseChangeHom' g 𝒜`, `T = O_{Proj_S 𝒜}(d)`, `T' = O_{Proj_{S'}(g^*𝒜)}(d)`,
`ι_U = projChart U`, `ι'_V = projChart V`, `ψ_i = Proj.map (unit : 𝒜(U) → (g^*𝒜)(V))`.

* `twistBaseChangeLeg i : T ⟶ (ι'_V ≫ φ)_* O_{Proj (g^*𝒜)(V)}(d)` is the limit projection `twistπ d U`
  followed by the ring-level transition map `Proj.twistPushTransition ψ_i` (Stacks 01MX, θ) —
  legitimate because `ι'_V ≫ φ = ψ_i ≫ ι_U` (`projChart_comp_baseChangeHom`).
* `twistBaseChangeSharp i : φ^* T ⟶ (ι'_V)_* O_V(d)` is its adjoint transpose (`pullback φ ⊣ pushforward φ`),
  `twistBaseChangeSigma i : (φ^* T).restrict ι'_V ⟶ O_V(d)` the further transpose along
  `restrictAdjunction ι'_V`.
* `twistChartTranspose d V : T'.restrict ι'_V ⟶ O_V(d)` is the transpose of `twistπ d V`; it is an
  isomorphism by Stacks 01LI (`isIso_restrictFunctor_map_twistπ`).
* `twistBaseChangePsi i := Sigma i ≫ (twistChartTranspose d V)⁻¹ : (φ^* T).restrict ι'_V ⟶ T'.restrict ι'_V`
  is the local comparison map, to be glued in `RelativeProjBaseChangeTwist`.

Compatibility along the transition maps of the small-chart cover (`k ≤ i`):
`twistBaseChangeLeg'_compat` (Stacks 01NP: `twistPushTransition` is transitive, `twistπ_transition`,
and the unit commutes with restriction, `restrictGraded_comp_baseChangeUnitGraded`),
hence `twistBaseChangeSharp_compat` (adjunction) and `twistBaseChangePsi_compat`
(`Modules.restrictTranspose_quot_compat`).

Source: Stacks 01O3, 01N2, 01MX, 01NP, 01LI; Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

-- Guard (as in `RelativeProjTwistLimit`): `O(m)` is an opaque module sheaf here.
attribute [local irreducible] AlgebraicGeometry.Proj.twist

namespace AlgebraicGeometry.Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Pushing a transition map `T(f) : (ι_A)_* O(n) ⟶ (ι_B)_* O(n)` forward along `φ : Y ⟶ Y'` gives
the transition map for `ι_A ≫ φ`, `ι_B ≫ φ` (all maps are identities on sections). -/
theorem pushforward_map_twistPushTransition (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    {Y Y' : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB) (φ : Y ⟶ Y') :
    (AlgebraicGeometry.Scheme.Modules.pushforward φ).map (twistPushTransition f hf n ιA ιB w) =
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp ιA φ).hom.app _ ≫
        twistPushTransition f hf n (ιA ≫ φ) (ιB ≫ φ) (by rw [← Category.assoc, w]) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp ιB φ).inv.app _ := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  simp only [twistPushTransition, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.pushforward_map_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_inv_app_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardCongr_hom_app_app]
  erw [Category.comp_id]
  rfl

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedAffineAlgebra)

theorem map_projChart' {U V : X.AffineZariskiSite} (h : U ≤ V) :
    Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) ≫ S.projChart V = S.projChart U := by
  have this := S.map_projChart h
  dsimp only [projFunctor] at this
  exact this

/-- `twistTransition` is the ring-level transition map (definitional unfolding). -/
theorem twistTransition_eq_twistPushTransition (m : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V) :
    S.twistTransition m h = Proj.twistPushTransition (S.restrictGraded h) (S.restrict_irrelevant_le h) m
      (S.projChart V) (S.projChart U) (S.map_projChart' h) := rfl

/-- The ring-level transition map in the shape `Modules.pushTransition` (definitional unfolding). -/
theorem twistPushTransition_eq_pushTransition (m : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V) :
    Proj.twistPushTransition (S.restrictGraded h) (S.restrict_irrelevant_le h) m
        (S.projChart V) (S.projChart U) (S.map_projChart' h) =
      Modules.pushTransition (S.projChart V) (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h))
        (S.projChart U) (S.map_projChart' h)
        (Proj.twistToPushforward (S.restrictGraded h) (S.restrict_irrelevant_le h) m) := rfl

/-- `twistTransition` in the shape `Modules.pushTransition`. (Two cheap unfoldings; the direct `rfl`
takes 35 s — the unifier picks a bad unfolding order.) -/
theorem twistTransition_eq_pushTransition (m : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V) :
    S.twistTransition m h =
      Modules.pushTransition (S.projChart V) (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h))
        (S.projChart U) (S.map_projChart' h)
        (Proj.twistToPushforward (S.restrictGraded h) (S.restrict_irrelevant_le h) m) :=
  (S.twistTransition_eq_twistPushTransition m h).trans (S.twistPushTransition_eq_pushTransition m h)

@[reassoc]
theorem twistπ_twistPushTransition (m : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V) :
    S.twistπ m V ≫ Proj.twistPushTransition (S.restrictGraded h) (S.restrict_irrelevant_le h) m
      (S.projChart V) (S.projChart U) (S.map_projChart' h) = S.twistπ m U := by
  rw [← S.twistTransition_eq_twistPushTransition m h]
  exact S.twistπ_transition m h

/-- `τ_U : O(m)|_{Proj S(U)} ⟶ O_U(m)`, the transpose of the limit projection `twistπ m U` along
`restrictFunctor ι_U ⊣ pushforward ι_U`. -/
def twistChartTranspose (m : ℤ) (U : X.AffineZariskiSite) :
    (S.twist m).restrict (S.projChart U) ⟶ Proj.twist (S.grading U) m :=
  Modules.restrictTranspose (S.projChart U) (S.twistπ m U)

/-- **Stacks 01LI**: `τ_U` is an isomorphism (`isIso_restrictFunctor_map_twistπ`). -/
theorem isIso_restrictTranspose_twistπ (m : ℤ) (U : X.AffineZariskiSite) :
    IsIso (Modules.restrictTranspose (S.projChart U) (S.twistπ m U)) :=
  Modules.isIso_restrictTranspose _ _ (S.isIso_restrictFunctor_map_twistπ m U)

theorem isIso_twistChartTranspose (m : ℤ) (U : X.AffineZariskiSite) :
    IsIso (S.twistChartTranspose m U) :=
  S.isIso_restrictTranspose_twistπ m U

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra) (d : ℤ)

/-- `baseChangeHom' g 𝒜` with source and target spelled through `GradedAffineAlgebra.relativeProj`
(the spelling of the charts `projChart` and of the twisting sheaves `twist`; `relativeProj S` is by
definition `S.toGradedAffineAlgebra.relativeProj`). Instance search and `rw` need one spelling. -/
def baseChangeHom' :
    (𝒜.pullback g).toGradedAffineAlgebra.relativeProj.left ⟶
      𝒜.toGradedAffineAlgebra.relativeProj.left :=
  baseChangeHom g 𝒜

theorem baseChangeHom'_eq : baseChangeHom' g 𝒜 = baseChangeHom g 𝒜 := rfl

/-- The unit graded hom `𝒜(U) →+*ᵍ (g^*𝒜)(V)` of a small chart `i = (U, V)`, typed on the gradings
`GradedAffineAlgebra.grading` (the spelling of `twistπ`, `restrictGraded`, `projChart`); a `def`, so
that every term built from it carries this spelling. -/
def baseChangeUnit (i : BaseChangeChartIndex g) :
    𝒜.toGradedAffineAlgebra.grading i.1.1 →+*ᵍ (𝒜.pullback g).toGradedAffineAlgebra.grading i.1.2 :=
  baseChangeUnitGraded g 𝒜 i.1.1.toOpens i.1.2.toOpens i.2

theorem baseChangeUnit_irrelevant_le (i : BaseChangeChartIndex g) :
    HomogeneousIdeal.irrelevant ((𝒜.pullback g).toGradedAffineAlgebra.grading i.1.2) ≤
      (HomogeneousIdeal.irrelevant (𝒜.toGradedAffineAlgebra.grading i.1.1)).map (baseChangeUnit g 𝒜 i) :=
  baseChangeUnitGraded_irrelevant_le g 𝒜 i.1.1.toOpens i.1.2.toOpens i.2 i.1.1.2 i.1.2.2

/-- `ψ_i ≫ ι_U = ι'_V ≫ φ` (`projChart_comp_baseChangeHom`, with `ψ_i` spelled as `Proj.map`). -/
theorem projMap_baseChangeUnit_comp_projChart (i : BaseChangeChartIndex g) :
    Proj.map (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) ≫
        𝒜.toGradedAffineAlgebra.projChart i.1.1 =
      (𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 ≫ baseChangeHom' g 𝒜 :=
  (projChart_comp_baseChangeHom g 𝒜 i).symm

/-- **Stacks 01N2, twisting sheaves** on the chart `i`, in the `grading` spelling
(`isIso_baseChangeProjMap_twistPullbackHom`). -/
theorem isIso_twistPullbackHom_baseChangeUnit (i : BaseChangeChartIndex g) :
    IsIso (Proj.twistPullbackHom (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) d) :=
  isIso_baseChangeProjMap_twistPullbackHom g 𝒜 i.1.1 i.1.2 i.2 d

/-- `ψ_i ≫ ι_U ≫ … `: the transition `Proj.map (restr')` composed with `ι'_i ≫ φ` is `ι'_k ≫ φ`. -/
theorem projMap_restrictGraded_comp_projChart_baseChangeHom' {k i : BaseChangeChartIndex g} (hki : k ≤ i) :
    Proj.map ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
        ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)) ≫
      ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2 ≫ baseChangeHom' g 𝒜) =
    (𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2 ≫ baseChangeHom' g 𝒜 := by
  rw [← Category.assoc, (𝒜.pullback g).toGradedAffineAlgebra.map_projChart' (BaseChangeChartIndex.le_V hki)]

/-! ### The local comparison data, as notation

The pieces below are **notation, not definitions**: unfolding a `def` whose body contains these terms
against a differently spelled but definitionally equal term costs 30–40 s in the unifier (nested
Prop-instance abstraction, cf. the compile-time remarks of `RelativeProjTwistLimit`), while
the literal terms are matched syntactically. All statements about them are therefore stated with the
literal terms; the notation only keeps them readable.

* `bcT[g, 𝒜, d, i] : (ι_U)_* O_U(d) ⟶ (ι'_V ≫ φ)_* O_V(d)`: the ring-level transition map along the
  unit `𝒜(U) → (g^*𝒜)(V)` (Stacks 01MX, θ), legitimate since `ψ_i ≫ ι_U = ι'_V ≫ φ`.
* `bcLeg[g, 𝒜, d, i] = twistπ d U ≫ bcT[…] : T ⟶ (ι'_V ≫ φ)_* O_V(d)` (`c_i`), and
  `bcLeg'[…] : T ⟶ φ_* (ι'_V)_* O_V(d)` (through `pushforwardComp`).
* `bcSharp[g, 𝒜, d, i] : φ^* T ⟶ (ι'_V)_* O_V(d)`: transpose along `pullback φ ⊣ pushforward φ`.
* `bcSigma[g, 𝒜, d, i] : (φ^* T)|_V ⟶ O_V(d)`: further transpose along `restrictAdjunction ι'_V`.
* `bcTau[g, 𝒜, d, i] : T'|_V ⟶ O_V(d)`: the transpose of `twistπ d V` (an isomorphism, 01LI).
* `bcPsi[g, 𝒜, d, i] = bcSigma[…] ≫ (bcTau[…])⁻¹ : (φ^* T)|_V ⟶ T'|_V`: the local comparison map. -/

set_option quotPrecheck false in
scoped notation "bcT[" g ", " 𝒜 ", " d ", " i "]" =>
  Proj.twistPushTransition (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) d
    ((𝒜).toGradedAffineAlgebra.projChart (i).1.1)
    (((𝒜).pullback g).toGradedAffineAlgebra.projChart (i).1.2 ≫ baseChangeHom' g 𝒜)
    (projMap_baseChangeUnit_comp_projChart g 𝒜 i)

set_option quotPrecheck false in
scoped notation "bcTr[" g ", " 𝒜 ", " d ", " hki "]" =>
  Proj.twistPushTransition (((𝒜).pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
    (((𝒜).pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)) d
    (((𝒜).pullback g).toGradedAffineAlgebra.projChart _ ≫ baseChangeHom' g 𝒜)
    (((𝒜).pullback g).toGradedAffineAlgebra.projChart _ ≫ baseChangeHom' g 𝒜)
    (projMap_restrictGraded_comp_projChart_baseChangeHom' g 𝒜 hki)

set_option quotPrecheck false in
scoped notation "bcPC[" g ", " 𝒜 ", " d ", " i "]" =>
  (Modules.pushforwardComp (((𝒜).pullback g).toGradedAffineAlgebra.projChart (i).1.2) (baseChangeHom' g 𝒜)).inv.app
    (Proj.twist (((𝒜).pullback g).toGradedAffineAlgebra.grading (i).1.2) d)

set_option quotPrecheck false in
scoped notation "bcLeg[" g ", " 𝒜 ", " d ", " i "]" =>
  (𝒜).toGradedAffineAlgebra.twistπ d (i).1.1 ≫ bcT[g, 𝒜, d, i]

set_option quotPrecheck false in
scoped notation "bcLeg'[" g ", " 𝒜 ", " d ", " i "]" =>
  bcLeg[g, 𝒜, d, i] ≫ bcPC[g, 𝒜, d, i]

set_option quotPrecheck false in
scoped notation "bcSharp[" g ", " 𝒜 ", " d ", " i "]" =>
  ((Modules.pullbackPushforwardAdjunction (baseChangeHom' g 𝒜)).homEquiv _ _).symm bcLeg'[g, 𝒜, d, i]

set_option quotPrecheck false in
scoped notation "bcSigma[" g ", " 𝒜 ", " d ", " i "]" =>
  Modules.restrictTranspose (((𝒜).pullback g).toGradedAffineAlgebra.projChart (i).1.2) bcSharp[g, 𝒜, d, i]

set_option quotPrecheck false in
scoped notation "bcTau[" g ", " 𝒜 ", " d ", " i "]" =>
  Modules.restrictTranspose (((𝒜).pullback g).toGradedAffineAlgebra.projChart (i).1.2)
    (((𝒜).pullback g).toGradedAffineAlgebra.twistπ d (i).1.2)

set_option quotPrecheck false in
scoped notation "bcPsi[" g ", " 𝒜 ", " d ", " i "]" => bcSigma[g, 𝒜, d, i] ≫ inv bcTau[g, 𝒜, d, i]

section Compat

variable {k i : BaseChangeChartIndex g} (hki : k ≤ i)

/-- `χ := restr' ∘ unit_i = unit_k ∘ restr` as ring homs (the unit commutes with restriction). -/
theorem baseChangeUnit_comp_eq :
    (((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki)).comp
        (baseChangeUnit g 𝒜 i)).toRingHom =
      (baseChangeUnit g 𝒜 k).toRingHom.comp
        (𝒜.toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_U hki)).toRingHom :=
  congrArg GradedRingHom.toRingHom (restrictGraded_comp_baseChangeUnitGraded g 𝒜 i.1.1 i.1.2 i.2
    (BaseChangeChartIndex.le_U hki) (BaseChangeChartIndex.le_V hki) k.2)

/-- `T(unit_i) ≫ T(restr') = T(restr' ∘ unit_i)` (Stacks 01NP). -/
@[reassoc]
theorem twistPushTransition_unit_restrict :
    bcT[g, 𝒜, d, i] ≫ bcTr[g, 𝒜, d, hki] =
    Proj.twistPushTransition
      (((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki)).comp (baseChangeUnit g 𝒜 i))
      (HomogeneousIdeal.irrelevant_le_map_comp (baseChangeUnit_irrelevant_le g 𝒜 i)
        ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki))) d
      (𝒜.toGradedAffineAlgebra.projChart i.1.1) ((𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2 ≫ baseChangeHom' g 𝒜)
      (by rw [Proj.map_comp (baseChangeUnit g 𝒜 i) ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
          (baseChangeUnit_irrelevant_le g 𝒜 i) ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)),
        Category.assoc, projMap_baseChangeUnit_comp_projChart g 𝒜 i,
        projMap_restrictGraded_comp_projChart_baseChangeHom' g 𝒜 hki]) :=
  (Proj.twistPushTransition_comp (baseChangeUnit g 𝒜 i)
    ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
    (((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki)).comp (baseChangeUnit g 𝒜 i))
    (baseChangeUnit_irrelevant_le g 𝒜 i) ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki))
    (HomogeneousIdeal.irrelevant_le_map_comp (baseChangeUnit_irrelevant_le g 𝒜 i)
      ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki))) d rfl _ _ _ _ _ _).symm

/-- `T(restr' ∘ unit_i) = T(restr) ≫ T(unit_k)` (Stacks 01NP + the unit commutes with restriction). -/
@[reassoc]
theorem twistPushTransition_restrict_unit :
    Proj.twistPushTransition
      (((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki)).comp (baseChangeUnit g 𝒜 i))
      (HomogeneousIdeal.irrelevant_le_map_comp (baseChangeUnit_irrelevant_le g 𝒜 i)
        ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki))) d
      (𝒜.toGradedAffineAlgebra.projChart i.1.1) ((𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2 ≫ baseChangeHom' g 𝒜)
      (by rw [Proj.map_comp (baseChangeUnit g 𝒜 i) ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
          (baseChangeUnit_irrelevant_le g 𝒜 i) ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)),
        Category.assoc, projMap_baseChangeUnit_comp_projChart g 𝒜 i,
        projMap_restrictGraded_comp_projChart_baseChangeHom' g 𝒜 hki]) =
    Proj.twistPushTransition (𝒜.toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_U hki))
      (𝒜.toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_U hki)) d
      (𝒜.toGradedAffineAlgebra.projChart i.1.1) (𝒜.toGradedAffineAlgebra.projChart k.1.1) (𝒜.toGradedAffineAlgebra.map_projChart' (BaseChangeChartIndex.le_U hki)) ≫
    bcT[g, 𝒜, d, k] :=
  Proj.twistPushTransition_comp (𝒜.toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_U hki))
    (baseChangeUnit g 𝒜 k)
    (((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki)).comp (baseChangeUnit g 𝒜 i))
    (𝒜.toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_U hki)) (baseChangeUnit_irrelevant_le g 𝒜 k)
    (HomogeneousIdeal.irrelevant_le_map_comp (baseChangeUnit_irrelevant_le g 𝒜 i)
      ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki))) d
    (baseChangeUnit_comp_eq g 𝒜 hki) _ _ _ _ _ _

/-- **Compatibility of the legs `c_i` with the transition maps** (Stacks 01NP, `twistπ_transition`). -/
theorem twistBaseChangeLeg'_compat :
    bcLeg'[g, 𝒜, d, k] = bcLeg'[g, 𝒜, d, i] ≫
      (Modules.pushforward (baseChangeHom' g 𝒜)).map
        ((𝒜.pullback g).toGradedAffineAlgebra.twistTransition d (BaseChangeChartIndex.le_V hki)) := by
  rw [GradedAffineAlgebra.twistTransition_eq_twistPushTransition,
    Proj.pushforward_map_twistPushTransition]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h1 := twistPushTransition_unit_restrict_assoc g 𝒜 d hki bcPC[g, 𝒜, d, k]
  have h2 := twistPushTransition_restrict_unit_assoc g 𝒜 d hki bcPC[g, 𝒜, d, k]
  have h3 := 𝒜.toGradedAffineAlgebra.twistπ_twistPushTransition_assoc d (BaseChangeChartIndex.le_U hki)
    (bcT[g, 𝒜, d, k] ≫ bcPC[g, 𝒜, d, k])
  exact ((congrArg (fun y => 𝒜.toGradedAffineAlgebra.twistπ d i.1.1 ≫ y) (h1.trans h2)).trans h3).symm

/-- Compatibility of `χ^♯` with the transition maps. -/
theorem twistBaseChangeSharp_compat :
    bcSharp[g, 𝒜, d, k] = bcSharp[g, 𝒜, d, i] ≫
      (𝒜.pullback g).toGradedAffineAlgebra.twistTransition d (BaseChangeChartIndex.le_V hki) := by
  rw [twistBaseChangeLeg'_compat g 𝒜 d hki]
  exact Adjunction.homEquiv_naturality_right_symm _ _ _

/-- **Compatibility of the local comparison maps `ψ_i = σ_i ≫ τ_V⁻¹`** with the transition maps of the
small-chart cover (spelled `Proj.map (restrictGraded _)`), in the form required by
`Modules.exists_hom_of_restrict_compat`. -/
theorem twistBaseChangePsi_compat :
    haveI := (𝒜.pullback g).toGradedAffineAlgebra.isOpenImmersion_projMap_restrictGraded (BaseChangeChartIndex.le_V hki)
    haveI := (𝒜.pullback g).toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d i.1.2
    haveI := (𝒜.pullback g).toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d k.1.2
    bcPsi[g, 𝒜, d, k] =
      (Modules.restrictCompIso
          (Proj.map ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
            ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)))
          ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2) ((𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2)
          ((𝒜.pullback g).toGradedAffineAlgebra.map_projChart' (BaseChangeChartIndex.le_V hki))).hom.app _ ≫
      (Modules.restrictFunctor
          (Proj.map ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
            ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)))).map bcPsi[g, 𝒜, d, i] ≫
      (Modules.restrictCompIso
          (Proj.map ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
            ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)))
          ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2) ((𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2)
          ((𝒜.pullback g).toGradedAffineAlgebra.map_projChart' (BaseChangeChartIndex.le_V hki))).inv.app _ := by
  haveI := (𝒜.pullback g).toGradedAffineAlgebra.isOpenImmersion_projMap_restrictGraded (BaseChangeChartIndex.le_V hki)
  haveI := (𝒜.pullback g).toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d i.1.2
  haveI := (𝒜.pullback g).toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d k.1.2
  exact Modules.restrictTranspose_quot_compat ((𝒜.pullback g).toGradedAffineAlgebra.projChart i.1.2)
    (Proj.map ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
      ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)))
    ((𝒜.pullback g).toGradedAffineAlgebra.projChart k.1.2) ((𝒜.pullback g).toGradedAffineAlgebra.map_projChart' (BaseChangeChartIndex.le_V hki))
    bcSharp[g, 𝒜, d, i] ((𝒜.pullback g).toGradedAffineAlgebra.twistπ d i.1.2)
    (Proj.twistToPushforward ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded (BaseChangeChartIndex.le_V hki))
      ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le (BaseChangeChartIndex.le_V hki)) d)
    bcSharp[g, 𝒜, d, k] ((𝒜.pullback g).toGradedAffineAlgebra.twistπ d k.1.2)
    ((twistBaseChangeSharp_compat g 𝒜 d hki).trans
      (congrArg (fun x => bcSharp[g, 𝒜, d, i] ≫ x)
        ((𝒜.pullback g).toGradedAffineAlgebra.twistTransition_eq_pushTransition d (BaseChangeChartIndex.le_V hki))))
    (((𝒜.pullback g).toGradedAffineAlgebra.twistπ_transition d (BaseChangeChartIndex.le_V hki)).symm.trans
      (congrArg (fun x => (𝒜.pullback g).toGradedAffineAlgebra.twistπ d i.1.2 ≫ x)
        ((𝒜.pullback g).toGradedAffineAlgebra.twistTransition_eq_pushTransition d (BaseChangeChartIndex.le_V hki))))

end Compat

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
