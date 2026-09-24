import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOverCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.P1MorphismOfForms
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStandardChart
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Chow.CurveDegreeEqTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjBundleFiberDegreeOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.Stacks0ayx
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.HomogeneousEquationSectionAtTotalSpaceSectionLemmas
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStdChartTrivialization
import MiyaokaMori.RingTheory.PolynomialTupleHomogenization

/-! # Binary forms on the projective line: degree and chart comparison

Statement: the projectivization to `P¹` defined by a tuple of binary forms of the same degree without common
zero pulls `O(1)` back to a line bundle whose degree is the homogeneous degree; on the standard affine chart, if the
forms are obtained from a tuple of polynomials by removing a common homogeneous factor, the projectivization agrees
with the local projectivization of the original polynomials.

Proof:
1. `projectivizationMorphism_pullback_twist` identifies the pullback of `O(1)` with the Serre twist of the
   homogeneous degree; `LineBundle.degree_ofModules_tensorPow` and `ProjectiveLine.degree_ofModules_twist_one`
   give the degree `d`.
2. For `d = 0` the map is constant: `projectivizationMorphism_isConstant_of_proportional`.
3. Chart comparison `morphismOfForms_stdChart_polynomialSection_homog`: by the uniqueness of Stacks 01NE
   (`projectiveSpace_hom_ext_of_sections`), build `θ : (O.ι ≫ stdChart ≫ [F])^*𝒪(1) ≅ 𝒪_O` and track sections
   (the general lemma `pullbackCompTrivIso_app`; the trivialization on the `stdChart` side is in
   `ProjectiveLineStdChartTrivialization`); the common factor `D(1,t)` is a unit by `hO` and is absorbed by
   `unitMulIso`.

Source: Theorem 4.2 of the paper; Debarre, Higher-Dimensional Algebraic Geometry §6.1; Stacks 01NE.

`sectionPullbackAlong` is the one definition (its body is the adjunction unit) and `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`
its `Γ`-typed reducible abbrev: `unfold sectionPullbackAlong` does not produce the `Γ`-typed spelling; the proof
below needs no bridge, since its `erw` steps unify the two spellings at default transparency. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- On a smooth projective curve, the tensor power `M^{⊗d}` (`Scheme.Modules.tensorPow`, recursion on the right) of
a line bundle `M` has degree `d · deg M`. Induction: `tensorPow M 0 = 𝒪` (`LineBundle.degree_one`),
`tensorPow M (e+1) = tensorPow M e ⊗ M` (`LineBundle.degree_eq_add_of_iso_tensor`, additivity of the degree,
Stacks 0AYX / Hartshorne II.6.13). -/
theorem LineBundle.degree_ofModules_tensorPow {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (M : C.toVariety.toScheme.Modules) [M.IsLineBundle] (d : ℕ) :
    LineBundle.degree (C := C)
        (LineBundle.ofModules (X := C.toVariety) (AlgebraicGeometry.Scheme.Modules.tensorPow M d)) =
      (d : ℤ) * LineBundle.degree (C := C) (LineBundle.ofModules (X := C.toVariety) M) := by
  induction d with
  | zero =>
      change LineBundle.degree (LineBundle.one C.toVariety) = _
      rw [LineBundle.degree_one]
      simp
  | succ e ih =>
      have h := LineBundle.degree_eq_add_of_iso_tensor
        (LineBundle.ofModules (X := C.toVariety) (AlgebraicGeometry.Scheme.Modules.tensorPow M e))
        (LineBundle.ofModules (X := C.toVariety) M)
        (LineBundle.ofModules (X := C.toVariety) (AlgebraicGeometry.Scheme.Modules.tensorPow M (e + 1)))
        (CategoryTheory.Iso.refl _)
      rw [h, ih]
      push_cast
      ring

/-- The degree of `𝒪(1)` on `P¹` is `1`: `LineBundle.degree` equals the top self-intersection of the Chow route
(`LineBundle.degree_eq_topSelfIntersection`), and the top self-intersection of `𝒪(1)` on `P^n` is `1`
(`projectiveSpace_top_selfIntersection_one` with `n = 1`). Properness comes from `P¹` being projective. -/
theorem ProjectiveLine.degree_ofModules_twist_one (k : Type u) [Field k] :
    LineBundle.degree (C := ProjectiveLine.asSmoothProjectiveCurve k)
      (LineBundle.ofModules (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
        (projectiveSpaceTwist k 1 1)) = 1 := by
  have hC : IsProperOver k (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp
      (ProjectiveLine.asSmoothProjectiveCurve k).projective).1
  rw [LineBundle.degree_eq_topSelfIntersection (ProjectiveLine.asSmoothProjectiveCurve k) hC]
  exact projectiveSpace_top_selfIntersection_one (K := k) 1 hC

theorem ProjectiveLine.degree_pullback_twist_of_forms {k : Type u} [Field k] [IsAlgClosed k]
    {N d : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin 2) k)
    (hF : ∀ j, (F j).IsHomogeneous d)
    (hF0 : ∀ v : Fin 2 → k, v ≠ 0 → ∃ j, MvPolynomial.eval v (F j) ≠ 0) :
    LineBundle.degree (C := ProjectiveLine.asSmoothProjectiveCurve k)
      (LineBundle.ofModules (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (ProjectiveLine.morphismOfForms F hF hF0)).obj (projectiveSpaceTwist k N 1))) =
      (d : ℤ) := by
  obtain ⟨θ, -⟩ := projectivizationMorphism_pullback_twist (k := k)
    (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k 1 1) d)
    (ProjectiveLine.formSections F hF) (ProjectiveLine.formSections_not_all_isZeroAt F hF hF0)
  rw [LineBundle.degree_congr (C := ProjectiveLine.asSmoothProjectiveCurve k)
    (L := LineBundle.ofModules (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (ProjectiveLine.morphismOfForms F hF hF0)).obj (projectiveSpaceTwist k N 1)))
    (M := LineBundle.ofModules (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
      (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k 1 1) d)) θ]
  rw [LineBundle.degree_ofModules_tensorPow, ProjectiveLine.degree_ofModules_twist_one]
  simp

-- The bridge lemma `ProjectiveLine.morphismOfForms_stdChart_polynomialSection` with Mathlib's `homogenize` convention
-- would be false (counterexample `P = (1,t)`, `F = (x₁,x₀)`); the corrected statement is
-- `morphismOfForms_stdChart_polynomialSection_homog` below.

section GenericSectionChase

variable {k : Type u} [Field k] {X Y Z : AlgebraicGeometry.Scheme.{u}}
  [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  (f : X ⟶ Y) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] (g : Y ⟶ Z)
  (L : Z.Modules) (B : Y.Modules) [B.IsLineBundle] {d : ℕ}
  (θF : (AlgebraicGeometry.Scheme.Modules.pullback g).obj L ≅
    AlgebraicGeometry.Scheme.Modules.tensorPow B d)
  (τ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj B ≅ SheafOfModules.unit X.ringCatSheaf)
  {u : Γ(X, ⊤)} (hu : IsUnit u)

/-- **Trivialization of `(f ≫ g)^*L` from a trivialization of `g^*L ≅ B^{⊗d}` and of `f^*B ≅ 𝒪_X`**, twisted by a
unit `u`: `(f ≫ g)^*L ≅ f^*(g^*L) ≅ f^*(B^{⊗d}) ≅ (f^*B)^{⊗d} ≅ 𝒪^{⊗d} ≅ 𝒪 --·u--> 𝒪`
(`pullbackComp`, `pullbackTensorPowIso`, `tensorPowMapIso`, `unitTensorPowIso`, `unitMulIso`).
Stated for variable schemes: the section chase `pullbackCompTrivIso_app` is done once here at the variable level
(on the concrete `P¹`-objects the same `erw` chain is far too slow). -/
def pullbackCompTrivIso :
    (AlgebraicGeometry.Scheme.Modules.pullback (f ≫ g)).obj L ≅ SheafOfModules.unit X.ringCatSheaf :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app L).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso θF ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f B d ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorPowMapIso τ d ≪≫
    AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X d ≪≫
    AlgebraicGeometry.Scheme.Modules.unitMulIso hu

set_option backward.isDefEq.respectTransparency false in
/-- Section formula: if `θF(g^*s) = F(c_0, …, c_M)` (`evalHomogeneousAtSections`), then
`pullbackCompTrivIso ((f ≫ g)^*s) = u · F(τ(f^*c_0), …, τ(f^*c_M))` (`MvPolynomial.eval₂` through the structure
map `k → Γ(X, 𝒪)`). Steps: `ModuleSections.pullback_comp_inv`, `pullback_naturality`,
`evalHomogeneousAtSections_pullback`, `evalHomogeneousAtSections_mapIso`, `evalHomogeneousAtSections_unit`,
`unitMulIso_hom_app_top`. -/
theorem pullbackCompTrivIso_app {M : ℕ} (F : MvPolynomial (Fin (M + 1)) k) (hF : F.IsHomogeneous d)
    (c : Fin (M + 1) → Γ(B, ⊤)) (s : Γ(L, ⊤))
    (hs : θF.hom.app ⊤ (sectionPullbackAlong g s) = evalHomogeneousAtSections B F hF c) :
    (pullbackCompTrivIso f g L B θF τ hu).hom.app ⊤ (sectionPullbackAlong (f ≫ g) s) =
      (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from
        u * MvPolynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
          (fun i => τ.hom.app ⊤ (sectionPullbackAlong f (c i))) F) := by
  unfold pullbackCompTrivIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  have h1 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv f g (M := L) s
  have h2 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_naturality (g := f) θF.hom
    (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g s)
  have h3 := evalHomogeneousAtSections_pullback f B F hF c
  -- `erw` (default transparency) sees through the reducible abbrev `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`, so no spelling
  -- bridge is needed here
  erw [h1, h2, hs, h3]
  rw [evalHomogeneousAtSections_mapIso τ F hF, evalHomogeneousAtSections_unit F hF,
    AlgebraicGeometry.Scheme.Modules.unitMulIso_hom_app_top]

end GenericSectionChase

/-- **Abstract form of the chart comparison.** Let `φF : P¹ → P^N` be a `k`-morphism with
`θF : φF^*𝒪(1) ≅ 𝒪(1)^{⊗d}` sending `φF^*x_i ↦ F_i(x₀, x₁)`, let `O ⊆ A¹` be open, `u ∈ Γ(O, 𝒪)` a unit and
`P'_j = u · F_j(1, t)` (`t := polynomialSection O X`) nowhere simultaneously vanishing. Then
`O.ι ≫ stdChart ≫ φF = projectivizationMorphism 𝒪_O P'`. Proof: Stacks 01NE uniqueness
(`projectiveSpace_hom_ext_of_sections`) with the trivialization `pullbackCompTrivIso` of `(O.ι ≫ stdChart ≫ φF)^*𝒪(1)`
built from `θF`, `stdChartPullbackTwistIso O` (`x₀ ↦ 1`, `x₁ ↦ t`) and `u`; the section formula
`pullbackCompTrivIso_app` gives `φ^*x_j ↦ u · F_j(1, t) = P'_j`. -/
theorem ProjectiveLine.stdChart_comp_eq_projectivization_of_pullback_twist
    {k : Type u} [Field k] {N d : ℕ}
    (F : Fin (N + 1) → MvPolynomial (Fin 2) k) (hF : ∀ j, (F j).IsHomogeneous d)
    (φF : ProjectiveLine k ⟶ ProjectiveSpace N k) [φF.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (θF : (AlgebraicGeometry.Scheme.Modules.pullback φF).obj (projectiveSpaceTwist k N 1) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k 1 1) d)
    (hθF : ∀ i, θF.hom.app ⊤ (sectionPullbackAlong φF (projectiveSpaceCoordinate k N i)) =
      evalHomogeneousAtSections (k := k) (projectiveSpaceTwist k 1 1) (F i) (hF i)
        (projectiveSpaceCoordinate k 1))
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens)
    (u : Γ(O.toScheme, ⊤)) (hu : IsUnit u)
    (P' : Fin (N + 1) → Γ(SheafOfModules.unit O.toScheme.ringCatSheaf, ⊤))
    (hP' : ∀ j, P' j = (show Γ(SheafOfModules.unit O.toScheme.ringCatSheaf, ⊤) from
      (u * MvPolynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (O.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
          ![1, polynomialSection O Polynomial.X] (F j) : Γ(O.toScheme, ⊤))))
    (hO : ∀ v : O.toScheme, ∃ ℓ, ¬ IsZeroAt (P' ℓ) v) :
    O.ι ≫ ProjectiveLine.stdChart k ≫ φF =
      projectivizationMorphism (k := k) (SheafOfModules.unit O.toScheme.ringCatSheaf) P' hO := by
  haveI hsc : (ProjectiveLine.stdChart k).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ProjectiveLine.stdChart_isOver k
  haveI hι₀ : (O.ι ≫ ProjectiveLine.stdChart k).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstance
  haveI hφ : ((O.ι ≫ ProjectiveLine.stdChart k) ≫ φF).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstance
  -- the coordinates of the trivialization `τ` of `(O.ι ≫ stdChart)^* 𝒪(1)`
  have hcoords : (fun j => (ProjectiveLine.stdChartPullbackTwistIso O).hom.app ⊤
      (sectionPullbackAlong (O.ι ≫ ProjectiveLine.stdChart k) (projectiveSpaceCoordinate k 1 j))) =
      (![1, polynomialSection O Polynomial.X] : Fin 2 → Γ(O.toScheme, ⊤)) := by
    funext j
    fin_cases j
    · exact ProjectiveLine.stdChartPullbackTwistIso_coordinate_zero O
    · exact ProjectiveLine.stdChartPullbackTwistIso_coordinate_one O
  rw [← Category.assoc]
  refine projectiveSpace_hom_ext_of_sections ((O.ι ≫ ProjectiveLine.stdChart k) ≫ φF)
    (SheafOfModules.unit O.toScheme.ringCatSheaf) P' hO
    (pullbackCompTrivIso (O.ι ≫ ProjectiveLine.stdChart k) φF (projectiveSpaceTwist k N 1)
      (projectiveSpaceTwist k 1 1) θF (ProjectiveLine.stdChartPullbackTwistIso O) hu) ?_
  intro i
  refine (pullbackCompTrivIso_app (O.ι ≫ ProjectiveLine.stdChart k) φF (projectiveSpaceTwist k N 1)
    (projectiveSpaceTwist k 1 1) θF (ProjectiveLine.stdChartPullbackTwistIso O) hu (F i) (hF i)
    (projectiveSpaceCoordinate k 1) (projectiveSpaceCoordinate k N i) (hθF i)).trans ?_
  rw [hcoords]
  exact (hP' i).symm

/-- **Chart comparison for the polynomial projectivization** (see the note above on the homogenization
convention). Let `P_0, …, P_N ∈ k[t]` with
`natDegree P_j ≤ r`, and let `homog (P_j) r = D · F_j` with `F_j` homogeneous of degree `d` and without common
zero on `P¹` (`homog p r = rename (swap 0 1) (homogenize p r)` is the homogenization adapted to the chart
`t ↦ [1 : t]`, `MiyaokaMori.RingTheory.PolynomialTupleHomogenization.eval₂_homog_one`). Then on every open `O ⊆ A¹` on which
the `P_j` have no common zero, the composite `O ↪ A¹ --stdChart--> P¹ --[F]--> P^N` equals the projectivization
of the tuple `(P_j(t))_j ∈ Γ(O, 𝒪)^{N+1}` (Stacks 01NE, `projectivizationMorphism` for the trivial line bundle).

Proof (Stacks 01NE uniqueness, `projectiveSpace_hom_ext_of_sections`): write
`ι := O.ι ≫ stdChart : O → P¹`, `φ_F := morphismOfForms F = projectivizationMorphism (𝒪(1)^{⊗d}) (F_j(x₀,x₁))`
and `φ := ι ≫ φ_F`. By 01NE it suffices to give `θ : φ^*𝒪_{P^N}(1) ≅ 𝒪_O` with `θ(φ^*x_j) = P_j(t)`:
1. `φ^*𝒪(1) ≅ ι^*(φ_F^*𝒪(1))` (`pullbackComp`) `≅ ι^*(𝒪(1)^{⊗d})` (`ι^*θ_F`, where
   `θ_F : φ_F^*𝒪(1) ≅ 𝒪(1)^{⊗d}` with `θ_F(φ_F^*x_j) = F_j(x₀,x₁)` is `projectivizationMorphism_pullback_twist`);
   sections: `φ^*x_j ↦ ι^*(F_j(x₀,x₁))` (`ModuleSections.pullback_comp_inv`, `pullback_naturality`).
2. `ι^*(𝒪(1)^{⊗d}) ≅ (ι^*𝒪(1))^{⊗d}` with `ι^*(F_j(x₀,x₁)) ↦ F_j(ι^*x₀, ι^*x₁)` (`evalHomogeneousAtSections_pullback`).
3. `τ : ι^*𝒪(1) ≅ 𝒪_O` with `ι^*x₀ ↦ 1`, `ι^*x₁ ↦ t := polynomialSection O X`
   (`ProjectiveLine.stdChartPullbackTwistIso`: the pullback of the authors' frame `x₀` of `𝒪(1)|_{D₊(x₀)}` along the
   chart map `O → D₊(x₀)`, whose ring map sends `x₁/x₀ ↦ t`); `τ^{⊗d}` maps `F_j(ι^*x₀, ι^*x₁) ↦ F_j(1, t)`
   (`evalHomogeneousAtSections_mapIso`) and `𝒪^{⊗d} ≅ 𝒪` identifies this with `eval₂ φ_k ![1, t] F_j`
   (`evalHomogeneousAtSections_unit`).
4. Common unit factor: `P_j(t) = eval₂ φ_k ![1,t] (homog P_j r) = u · F_j(1,t)` with `u := D(1,t)`
   (`polynomialSection_eq_eval₂`, `eval₂_homog_one`, `hfactor`). By `hO`, at every point of `O` some `P_j = u · F_j(1,t)`
   is nonvanishing, hence `u` is a unit (`isUnit_of_forall_exists_not_isZeroAt_smul`); multiplication by `u`
   is an automorphism `unitMulIso` of `𝒪_O` with `F_j(1,t) ↦ P_j(t)`.
Chain 1–4 to get `θ`; `projectiveSpace_hom_ext_of_sections` gives `φ = projectivizationMorphism 𝒪_O (P_j(t))`.
The `k`-structure hypotheses come from `ProjectiveLine.stdChart_isOver` and `projectivizationMorphism_isOver`.
Source: Stacks 01NE; Hartshorne II.7.1; §3 of the paper (the chart `t ↦ [1:t]`), Theorem 4.2 of the paper. -/
theorem ProjectiveLine.morphismOfForms_stdChart_polynomialSection_homog
    {k : Type u} [Field k] [IsAlgClosed k] {N d dD r : ℕ}
    (P : Fin (N + 1) → Polynomial k) (hdeg : ∀ j, (P j).natDegree ≤ r)
    (F : Fin (N + 1) → MvPolynomial (Fin 2) k)
    (D : MvPolynomial (Fin 2) k)
    (hF : ∀ j, (F j).IsHomogeneous d) (hD : D.IsHomogeneous dD) (hD0 : D ≠ 0)
    (hF0 : ∀ v : Fin 2 → k, v ≠ 0 → ∃ j, MvPolynomial.eval v (F j) ≠ 0)
    (hfactor : ∀ j, MiyaokaMori.RingTheory.PolynomialTupleHomogenization.homog (P j) r = D * F j) :
    ∀ (O : (AlgebraicGeometry.Scheme.affineLineOver
        (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens)
      (hO : ∀ v : O.toScheme, ∃ ℓ, ¬ IsZeroAt (polynomialSection O (P ℓ)) v),
      O.ι ≫ ProjectiveLine.stdChart k ≫ ProjectiveLine.morphismOfForms F hF hF0 =
        projectivizationMorphism (k := k) (SheafOfModules.unit O.toScheme.ringCatSheaf)
          (fun ℓ ↦ polynomialSection O (P ℓ)) hO := by
  intro O hO
  unfold ProjectiveLine.morphismOfForms
  obtain ⟨θF, hθF⟩ := projectivizationMorphism_pullback_twist (k := k)
    (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k 1 1) d)
    (ProjectiveLine.formSections F hF) (ProjectiveLine.formSections_not_all_isZeroAt F hF hF0)
  -- `P_j(t) = D(1,t) · F_j(1,t)` in `Γ(O, 𝒪)`, with `t := polynomialSection O X`
  have hPQ : ∀ j, polynomialSection O (P j) =
      (show Γ(SheafOfModules.unit O.toScheme.ringCatSheaf, ⊤) from
        (MvPolynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (O.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
          ![1, polynomialSection O Polynomial.X] D *
        MvPolynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (O.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
          ![1, polynomialSection O Polynomial.X] (F j) : Γ(O.toScheme, ⊤))) := by
    intro j
    rw [ProjectiveLine.polynomialSection_eq_eval₂ O (P j),
      ← MiyaokaMori.RingTheory.PolynomialTupleHomogenization.eval₂_homog_one (P j) (hdeg j), hfactor j,
      MvPolynomial.eval₂_mul]
  -- `D(1,t)` is a unit on `O`: at every point some `P_j(t) = D(1,t) · F_j(1,t)` is nonvanishing
  have hunit : IsUnit (MvPolynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (O.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
        ![1, polynomialSection O Polynomial.X] D) := by
    refine AlgebraicGeometry.Scheme.Modules.isUnit_of_forall_exists_not_isZeroAt_smul
      (M := SheafOfModules.unit O.toScheme.ringCatSheaf) _
      (fun j => (show Γ(SheafOfModules.unit O.toScheme.ringCatSheaf, ⊤) from
        (MvPolynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (O.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
          ![1, polynomialSection O Polynomial.X] (F j) : Γ(O.toScheme, ⊤)))) ?_
    intro v
    obtain ⟨ℓ, hℓ⟩ := hO v
    refine ⟨ℓ, ?_⟩
    rw [hPQ ℓ] at hℓ
    exact hℓ
  exact ProjectiveLine.stdChart_comp_eq_projectivization_of_pullback_twist F hF _ θF hθF O _ hunit _
    hPQ hO

/-! ## Tools for constancy (`d = 0`)

For `d = 0`, `morphismOfForms F` is given by the constants `c_j = F_j` and is the constant morphism
`[c_0 : ⋯ : c_N]`. The proof goes through the underlying map: a point of `Proj 𝒜` is determined by the
positive-degree basic opens `D₊(r)` containing it (`Proj.ext_of_mem_basicOpen_pos`, using the `T₀` property and
`isTopologicalBasis_basic_opens`; degree-`0` elements are reduced to positive degree using relevance of the prime),
while for a proportional tuple of sections `P_j = φ(c_j) • s` the chart `V_{ℓ₀}` (`c_{ℓ₀} ≠ 0`) is all of `V` and the
chart ring map `x_j ↦ c_j / c_{ℓ₀}` factors through `k`, so the preimage of `D₊(r)` is `⊤` or `⊥`
(`fromOfGlobalSections_preimage_basicOpen` and `basicOpen_of_isUnit`), independently of the point.
Source: Stacks 01NE (the chart description of the projectivization); Hartshorne II.7.1. -/

/-- The zero section vanishes everywhere. -/
theorem IsZeroAt.zero {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} (x : X) :
    IsZeroAt (0 : Γ(M, ⊤)) x := by
  change M.presheaf.germ ⊤ x trivial 0 ∈ _
  rw [map_zero]
  exact Submodule.zero_mem _

/-- A section vanishing at `x` still vanishes at `x` after multiplication by any function. -/
theorem IsZeroAt.smul {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    {s : Γ(M, ⊤)} {x : X} (h : IsZeroAt s x) (a : Γ(X, ⊤)) :
    IsZeroAt (a • s : Γ(M, ⊤)) x := by
  have hkey : M.presheaf.germ ⊤ x trivial (a • s) =
      X.presheaf.germ ⊤ x trivial a • M.presheaf.germ ⊤ x trivial s :=
    AlgebraicGeometry.Scheme.Modules.germ_smul' M (V := ⊤) (y := x) trivial a s
  have hmem : X.presheaf.germ ⊤ x trivial a • M.presheaf.germ ⊤ x trivial s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (M.stalk x)) :=
    Submodule.smul_mem _ _ h
  show M.presheaf.germ ⊤ x trivial (a • s) ∈ _
  rw [hkey]
  exact hmem

/-- If `a` is a unit and `a • s` vanishes at `x`, then `s` vanishes at `x`. -/
theorem IsZeroAt.of_smul_of_isUnit {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    {s : Γ(M, ⊤)} {x : X} {a : Γ(X, ⊤)}
    (h : IsZeroAt (a • s : Γ(M, ⊤)) x) (ha : IsUnit a) : IsZeroAt s x := by
  obtain ⟨u, rfl⟩ := ha
  have := h.smul (↑u⁻¹ : Γ(X, ⊤))
  rwa [smul_smul, Units.inv_mul, one_smul] at this

/-- **A point of `Proj 𝒜` is determined by the positive-degree basic opens**: if `p ∈ D₊(r) ↔ q ∈ D₊(r)` for all
`n > 0` and `r ∈ 𝒜 n`, then `p = q`.
Proof: `ProjectiveSpectrum.ext` and `HomogeneousIdeal.ext'` reduce to membership of homogeneous elements `r ∈ 𝒜 i`.
For `i > 0` this is the hypothesis; for `i = 0`, since `p` is relevant (does not contain the irrelevant ideal) pick a
positive-degree homogeneous `t ∉ p`; primality of `p` gives `r ∈ p ↔ r t ∈ p` with `r t` of positive degree, and
`t ∉ q` also by hypothesis, so the same holds on the `q` side. -/
theorem AlgebraicGeometry.Proj.ext_of_mem_basicOpen_pos {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {p q : AlgebraicGeometry.Proj 𝒜}
    (h : ∀ n, 0 < n → ∀ r ∈ 𝒜 n,
      (p ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 r ↔ q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 r)) :
    p = q := by
  have h' : ∀ n, 0 < n → ∀ r ∈ 𝒜 n, (r ∈ p.asHomogeneousIdeal ↔ r ∈ q.asHomogeneousIdeal) := by
    intro n hn r hr
    have := h n hn r hr
    simp only [AlgebraicGeometry.Proj.mem_basicOpen] at this
    exact not_iff_not.mp this
  -- a positive-degree homogeneous element outside `p`
  obtain ⟨m, hm, t, htm, htp⟩ : ∃ m, 0 < m ∧ ∃ t ∈ 𝒜 m, t ∉ p.asHomogeneousIdeal := by
    obtain ⟨t, ht, htp⟩ := SetLike.not_le_iff_exists.mp p.not_irrelevant_le
    rw [HomogeneousIdeal.mem_irrelevant_iff] at ht
    have hdec := Ideal.IsHomogeneous.mem_iff 𝒜 p.asHomogeneousIdeal.isHomogeneous (x := t)
    have : ¬ ∀ i, (DirectSum.decompose 𝒜 t i : A) ∈ p.asHomogeneousIdeal.toIdeal := by
      intro H
      exact htp (hdec.mpr H)
    obtain ⟨i, hi⟩ := not_forall.mp this
    refine ⟨i, ?_, (DirectSum.decompose 𝒜 t i : A), SetLike.coe_mem _, hi⟩
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      exfalso
      apply hi
      rw [← GradedRing.proj_apply, ht]
      exact Ideal.zero_mem _
    · exact h0
  have htq : t ∉ q.asHomogeneousIdeal := fun htq => htp ((h' m hm t htm).mpr htq)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro i r hr
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have hrt : r * t ∈ 𝒜 m := by
      have := SetLike.mul_mem_graded hr htm
      rwa [zero_add] at this
    have key := h' m hm (r * t) hrt
    constructor
    · intro hrp
      have : r * t ∈ q.asHomogeneousIdeal := key.mp (Ideal.mul_mem_right t _ hrp)
      exact (q.isPrime.mem_or_mem this).resolve_right htq
    · intro hrq
      have : r * t ∈ p.asHomogeneousIdeal := key.mpr (Ideal.mul_mem_right t _ hrq)
      exact (p.isPrime.mem_or_mem this).resolve_right htp
  · exact h' i hi r hr

section ProjectivizationConstant

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The projectivization of a proportional tuple of sections is a constant morphism**: if `P_j = φ(c_j) • s`
(`φ : k → Γ(V, 𝒪)` the structure map, `c_j ∈ k`), then the underlying map of
`projectivizationMorphism M P hP : V → P^N` is constant (with value `[c_0 : ⋯ : c_N]`).
Proof: pick `x₀ ∈ V` and `ℓ₀` with `P_{ℓ₀}` nonvanishing at `x₀`, so `c_{ℓ₀} ≠ 0`; for every `v` some
`P_j = φ(c_j) • s` is nonvanishing at `v`, hence `s` is, hence `P_{ℓ₀}` is: the chart `V_{ℓ₀}` is all of `V`. The
ratios are `r_{ℓ₀,j} = φ(c_j / c_{ℓ₀})` (`projectivizationRatio_unique`), and the chart ring map `x_j ↦ r_{ℓ₀,j}`
equals `ψ ∘ eval_{c/c_{ℓ₀}}` (`ψ` the structure map of `V_{ℓ₀}`), so the preimage of `D₊(r)` along the chart
morphism is `V_{ℓ₀}.basicOpen (ψ a)` (`fromOfGlobalSections_preimage_basicOpen`) with `a = r(c / c_{ℓ₀})`, which is
`⊤` (`a ≠ 0`, `basicOpen_of_isUnit`) or `⊥` (`a = 0`). Hence the underlying map sends any two points into the same
positive-degree basic opens, and they are equal by `Proj.ext_of_mem_basicOpen_pos`.
Source: Stacks 01NE; Hartshorne II.7.1. -/
theorem projectivizationMorphism_isConstant_of_proportional {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Nonempty V] (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v)
    (c : Fin (N + 1) → k) (s : Γ(M, ⊤))
    (hPc : ∀ j, P j = (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom (c j) : Γ(V, ⊤)) • s) :
    IsConstantMorphism (projectivizationMorphism (k := k) M P hP) := by
  set φ : k →+* Γ(V, ⊤) := ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom with hφ
  obtain ⟨x₀⟩ := ‹Nonempty V›
  obtain ⟨ℓ₀, hℓ₀⟩ := hP x₀
  have hc₀ : c ℓ₀ ≠ 0 := by
    intro h0
    apply hℓ₀
    rw [hPc, h0, map_zero, zero_smul]
    exact IsZeroAt.zero x₀
  have hchart : ∀ v : V, v ∈ projectivizationChart P ℓ₀ := by
    intro v
    obtain ⟨j, hj⟩ := hP v
    change ¬ IsZeroAt (P ℓ₀) v
    intro hz
    apply hj
    rw [hPc] at hz ⊢
    exact (hz.of_smul_of_isUnit ((isUnit_iff_ne_zero.mpr hc₀).map φ)).smul _
  have hratio : ∀ j, projectivizationRatio P ℓ₀ j =
      V.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ₀ ≤ ⊤)).op (φ (c j / c ℓ₀)) := by
    intro j
    apply projectivizationRatio_unique
    rw [AlgebraicGeometry.Scheme.Modules.res_self, hPc, hPc,
      AlgebraicGeometry.Scheme.Modules.res_smul, AlgebraicGeometry.Scheme.Modules.res_smul,
      smul_smul, ← map_mul, ← map_mul, div_mul_cancel₀ _ hc₀]
  set ψ : k →+* Γ((projectivizationChart P ℓ₀).toScheme, ⊤) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      ((projectivizationChart P ℓ₀).ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
    with hψ
  have hψφ : ∀ a : k, (projectivizationChart P ℓ₀).topIso.inv.hom
      (V.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ₀ ≤ ⊤)).op (φ a)) = ψ a := by
    intro a
    have hcomp : V.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ₀ ≤ ⊤)).op ≫
        (projectivizationChart P ℓ₀).topIso.inv = (projectivizationChart P ℓ₀).ι.appTop := by
      show V.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ₀ ≤ ⊤)).op ≫
          V.presheaf.map (eqToHom (projectivizationChart P ℓ₀).ι_image_top).op =
        V.presheaf.map (homOfLE (x := (projectivizationChart P ℓ₀).ι ''ᵁ ⊤) le_top).op
      rw [← V.presheaf.map_comp]
      rfl
    have key : ∀ y : Γ(V, ⊤), (projectivizationChart P ℓ₀).topIso.inv.hom
        (V.presheaf.map (homOfLE (le_top : projectivizationChart P ℓ₀ ≤ ⊤)).op y) =
        (projectivizationChart P ℓ₀).ι.appTop.hom y := by
      intro y
      have := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hcomp) y
      rwa [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [hψ, hφ]
    change _ = ((projectivizationChart P ℓ₀).ι ≫
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
    rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact key _
  have heval : ∀ r, projectivizationChartEval (k := k) P ℓ₀ r =
      ψ (MvPolynomial.eval (fun j => c j / c ℓ₀) r) := by
    intro r
    have : projectivizationChartEval (k := k) P ℓ₀ =
        ψ.comp (MvPolynomial.eval (fun j => c j / c ℓ₀)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [projectivizationChartEval, projectivizationChartEvalOver, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
          MvPolynomial.eval_C]
      · intro j
        rw [projectivizationChartEval, projectivizationChartEvalOver, MvPolynomial.eval₂Hom_X', hratio, hψφ, RingHom.comp_apply,
          MvPolynomial.eval_X]
    rw [this, RingHom.comp_apply]
  have hmem : ∀ (x : V) (n : ℕ), 0 < n → ∀ (r : MvPolynomial (Fin (N + 1)) k),
      r ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k n →
      ((projectivizationMorphism (k := k) M P hP).base x ∈
          AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) r ↔
        MvPolynomial.eval (fun j => c j / c ℓ₀) r ≠ 0) := by
    intro x n hn r hr
    let x' : (projectivizationChart P ℓ₀).toScheme := ⟨x, hchart x⟩
    have hx : (projectivizationMorphism (k := k) M P hP).base x =
        (projectivizationChartMorphism (k := k) P ℓ₀).base x' := by
      rw [← projectivizationMorphism_restrict M P hP ℓ₀]
      rfl
    rw [hx]
    change x' ∈ (projectivizationChartMorphism (k := k) P ℓ₀) ⁻¹ᵁ
      (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) r) ↔ _
    rw [show (projectivizationChartMorphism (k := k) P ℓ₀) ⁻¹ᵁ
        (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) r) =
        (projectivizationChart P ℓ₀).toScheme.basicOpen (projectivizationChartEval (k := k) P ℓ₀ r) from
      AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr, heval]
    by_cases ha : MvPolynomial.eval (fun j => c j / c ℓ₀) r = 0
    · rw [ha, map_zero, AlgebraicGeometry.Scheme.basicOpen_zero]
      simp
    · rw [AlgebraicGeometry.Scheme.basicOpen_of_isUnit _ ((isUnit_iff_ne_zero.mpr ha).map ψ)]
      simp [ha]
  refine ⟨(projectivizationMorphism (k := k) M P hP).base x₀, fun x => ?_⟩
  apply AlgebraicGeometry.Proj.ext_of_mem_basicOpen_pos
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
  intro n hn r hr
  exact (hmem x n hn r hr).trans (hmem x₀ n hn r hr).symm

end ProjectivizationConstant

/-- The "section" `evalHomogeneousAtSections A F hF f ∈ Γ(A^{⊗0}) = Γ(𝒪)` of a form `F` of degree `0` is the image of
the constant `F(0) = coeff 0 F` under the structure map (times `1`): the sum has only the term `α = 0`, and the
degree-`0` monomial section is `1`. -/
theorem evalHomogeneousAtSections_degree_zero {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (A : X.Modules) [A.IsLineBundle] {N : ℕ} (F : MvPolynomial (Fin (N + 1)) k)
    (hF : F.IsHomogeneous 0) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    evalHomogeneousAtSections (k := k) A F hF f =
      (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom (F.coeff 0)) •
        (show ((AlgebraicGeometry.Scheme.Modules.tensorPow A 0).val.obj (Opposite.op ⊤) : Type u) from
          (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))) := by
  unfold evalHomogeneousAtSections
  have hmono : ∀ g : Fin 0 → Fin (N + 1),
      evalHomogeneousAtSections.monomial A f 0 g =
        (show ((AlgebraicGeometry.Scheme.Modules.tensorPow A 0).val.obj (Opposite.op ⊤) : Type u) from
          (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))) := fun _ => rfl
  simp only [hmono]
  rw [Finset.sum_attach F.support (fun α => (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom (F.coeff α)) •
        (show ((AlgebraicGeometry.Scheme.Modules.tensorPow A 0).val.obj (Opposite.op ⊤) : Type u) from
          (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))))]
  apply Finset.sum_eq_single 0
  · intro b hb hb0
    exfalso
    apply hb0
    rw [← Finsupp.degree_eq_zero_iff]
    by_contra hdeg
    exact MvPolynomial.mem_support_iff.mp hb (hF.coeff_eq_zero hdeg)
  · intro h0
    rw [MvPolynomial.notMem_support_iff.mp h0, map_zero]
    dsimp only
    exact zero_smul (X.ringCatSheaf.obj.obj (Opposite.op ⊤))
      (show ((AlgebraicGeometry.Scheme.Modules.tensorPow A 0).val.obj (Opposite.op ⊤) : Type u) from
        (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤)))

theorem ProjectiveLine.constant_of_morphismOfForms_degree_zero
    {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ}
    (F : Fin (N + 1) → MvPolynomial (Fin 2) k)
    (hF : ∀ j, (F j).IsHomogeneous 0)
    (hF0 : ∀ v : Fin 2 → k, v ≠ 0 → ∃ j, MvPolynomial.eval v (F j) ≠ 0) :
    IsConstantMorphism (ProjectiveLine.morphismOfForms F hF hF0) := by
  have : Nonempty (ProjectiveLine k) :=
    @IrreducibleSpace.toNonempty _ _ (AlgebraicGeometry.Proj.ProjectiveLineIrreducible.projectiveLine_irreducible k)
  unfold ProjectiveLine.morphismOfForms
  refine projectivizationMorphism_isConstant_of_proportional _ _ _ (fun j => (F j).coeff 0)
    (show ((AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k 1 1) 0).val.obj
        (Opposite.op ⊤) : Type u) from (1 : (ProjectiveLine k).ringCatSheaf.obj.obj (Opposite.op ⊤)))
    (fun j => ?_)
  exact evalHomogeneousAtSections_degree_zero (projectiveSpaceTwist k 1 1) (F j) (hF j)
    (projectiveSpaceCoordinate k 1)

theorem ProjectiveLine.one_le_degree_of_nonconstant_morphismOfForms
    {k : Type u} [Field k] [IsAlgClosed k] {N d : ℕ}
    (F : Fin (N + 1) → MvPolynomial (Fin 2) k)
    (hF : ∀ j, (F j).IsHomogeneous d)
    (hF0 : ∀ v : Fin 2 → k, v ≠ 0 → ∃ j, MvPolynomial.eval v (F j) ≠ 0)
    (hnc : ¬ IsConstantMorphism (ProjectiveLine.morphismOfForms F hF hF0)) :
    1 ≤ d := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hd
  subst d
  exact hnc (ProjectiveLine.constant_of_morphismOfForms_degree_zero F hF hF0)

end
