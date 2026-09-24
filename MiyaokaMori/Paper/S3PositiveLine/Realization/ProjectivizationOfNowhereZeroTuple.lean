import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveVanishingIdealLocalization
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveVanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueIsoOfFrames
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ProjectivizationChartLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleChartPullback
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveCoordinateRatio
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverChartRatio
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousTupleLocalCoordinates
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbeddingGlobalFactorization
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveChartEquationEvaluation
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SeedHomogeneousConeFractions
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectivizationOverRing

/-! # The projectivization of a nowhere-zero tuple of sections

A tuple `(P_0,…,P_N)` of global sections of a line bundle `M` that are nowhere all zero induces a morphism
`V → P^N` pulling `O(1)` back to `M`; if the forms `F_j` vanish after substituting the `P_ℓ`, the morphism factors
through `X` (proof of Theorem 4.2 of the paper).

The construction itself lives in `AlgebraicGeometry/Proj/ProjectiveSpace/ProjectivizationOverRing`
(`projectivizationMorphismOver f M P hP` over any base ring `R` and any `f : V ⟶ Spec R`). This module provides the
field-level names as `abbrev`s at `R := k`, `f := V ↘ Spec k` (`projectivizationChartEval`,
`projectivizationChartMorphism`, `projectivizationCover`, `projectivizationMorphism`, `projectivizationChartMap`)
and restates their basic lemmas as one-line instances of the `…Over` lemmas. The base-free charts `V_ℓ`, the ratios
`r_{ℓ,j}` and the frame lemmas (`IsFrame.of_iSup`, `isFrame_res_nonvanishingLocus`, …) are in the primary module.
What remains here is field-specific: the `Over`-instance, the `φ^*O(1) ≅ M` comparison (step 5), and the
factorization through a projective embedding (step 6); the predicate `IsVanishingLocus` lives in
`AlgebraicGeometry/Proj/ProjectiveSpace/ProjectiveVanishingLocus`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The field-level names, as `abbrev`s of the over-ring primary -/

/-- The ring map `k[x_0,…,x_N] → Γ(V_ℓ, O)` on `V_ℓ`, `x_j ↦ r_{ℓ,j}` (`k` acting through the structure morphism).
`abbrev` of `projectivizationChartEvalOver (V ↘ Spec k) P ℓ`. -/
abbrev projectivizationChartEval {k : Type u} [Field k] {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) k →+* Γ((projectivizationChart P ℓ).toScheme, ⊤) :=
  projectivizationChartEvalOver (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) P ℓ

/-- `x_ℓ` takes the value `r_{ℓ,ℓ} = 1` on `V_ℓ`. -/
theorem projectivizationChartEval_X_self {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    projectivizationChartEval (k := k) P ℓ (MvPolynomial.X ℓ) = 1 :=
  projectivizationChartEvalOver_X_self _ P ℓ

/-- The image of the irrelevant ideal is the unit ideal: `x_ℓ` is homogeneous of degree `1` (hence in the irrelevant ideal) and its image is `1`. -/
theorem projectivizationChartEval_irrelevant_map_eq_top {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal.map
        (projectivizationChartEval (k := k) P ℓ) = ⊤ :=
  projectivizationChartEvalOver_irrelevant_map_eq_top _ P ℓ

/-- `V_ℓ → P^N`: `Proj.fromOfGlobalSections` (`x_ℓ ↦ r_{ℓ,ℓ} = 1`, so the image of the irrelevant ideal generates the unit ideal).
`abbrev` of `projectivizationChartMorphismOver (V ↘ Spec k) P ℓ`. -/
abbrev projectivizationChartMorphism {k : Type u} [Field k] {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    (projectivizationChart P ℓ).toScheme ⟶ ProjectiveSpace N k :=
  projectivizationChartMorphismOver (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) P ℓ

/-- The `V_ℓ` form an open cover of `V` (`hP`: the `P_ℓ` have no common zero). `abbrev` of the base-free `projectivizationCoverOver`. -/
abbrev projectivizationCover {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) : V.OpenCover :=
  projectivizationCoverOver M P hP

/-- The morphisms on two charts agree on the overlap `V_ℓ ∩ V_m` (`projectivizationChartMorphismOver_agree`). -/
theorem projectivizationChartMorphism_agree {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    ∀ x y : (projectivizationCover (k := k) M P hP).I₀,
      CategoryTheory.Limits.pullback.fst ((projectivizationCover (k := k) M P hP).f x)
            ((projectivizationCover (k := k) M P hP).f y) ≫
          projectivizationChartMorphism (k := k) P x =
        CategoryTheory.Limits.pullback.snd ((projectivizationCover (k := k) M P hP).f x)
            ((projectivizationCover (k := k) M P hP).f y) ≫
          projectivizationChartMorphism (k := k) P y :=
  projectivizationChartMorphismOver_agree _ M P hP

/-- **The projectivization morphism** `φ : V ⟶ P^N_k`, glued from the chart morphisms.
`abbrev` of `projectivizationMorphismOver (V ↘ Spec k) M P hP`. -/
abbrev projectivizationMorphism {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    V ⟶ ProjectiveSpace N k :=
  projectivizationMorphismOver (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) M P hP

/-- The glued projectivization restricts to its prescribed chart morphism. -/
theorem projectivizationMorphism_restrict {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ : Fin (N + 1)) :
    (projectivizationChart P ℓ).ι ≫
        projectivizationMorphism (k := k) M P hP =
      projectivizationChartMorphism (k := k) P ℓ :=
  projectivizationMorphismOver_restrict _ M P hP ℓ

/-- The glued morphism is a `Spec k`-morphism (`projectivizationMorphismOver_comp_toSpecBase`; `P^N_k ↘ Spec k` is
`ProjectiveSpaceOver.toSpecBase N k` by definition). -/
theorem projectivizationMorphism_comp_over {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    projectivizationMorphism (k := k) M P hP ≫
        ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k) =
      V ↘ AlgebraicGeometry.Spec (CommRingCat.of k) :=
  projectivizationMorphismOver_comp_toSpecBase _ M P hP

instance projectivizationMorphism_isOver {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    (projectivizationMorphism (k := k) M P hP).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨projectivizationMorphism_comp_over (k := k) M P hP⟩

/-- **`φ⁻¹(D_+(x_i)) = V_i`** (`projectivizationMorphismOver_preimage_basicOpen`). -/
theorem projectivizationMorphism_preimage_basicOpen {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (i : Fin (N + 1)) :
    projectivizationMorphism (k := k) M P hP ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i) =
      projectivizationChart P i :=
  projectivizationMorphismOver_preimage_basicOpen _ M P hP i

/-! ## Step 5: `φ^*O(1) ≅ M` with `φ^*x_j ↦ P_j`

Chart by chart: on `V_ℓ`, `φ` lands in `D_+(x_ℓ)`, and the chart morphism `g_ℓ : V_ℓ → D_+(x_ℓ)` is
`ProjectiveSpaceOverChart.chartMap` (the `Γ`–`Spec` adjunction; `chartMap_ι` says that composed with the open
immersion it is `fromOfGlobalSections`). On the target side `x_ℓ` is a frame of `O(1)|_{D_+(x_ℓ)}` (`targetFrameIso`),
so `φ^*x_ℓ` is a frame of `φ^*O(1)|_{V_ℓ}` (`pullbackFrameIso`), with the coordinate formula
`φ^*x_j ↦ g_ℓ^♯(x_j/x_ℓ) = r_{ℓ,j}` (`chartMap_appTop_ratio_mul`, `x_ℓ ↦ 1`). On the source side `P_ℓ` is a frame of
`M|_{V_ℓ}` (`projectivizationChart_isFrame`); with `θ_ℓ := (frame P_ℓ)⁻¹ ∘ (frame φ^*x_ℓ)` we get
`θ_ℓ(φ^*x_j) = r_{ℓ,j} • P_ℓ = P_j`. Finally glue along `{V_ℓ}` with `exists_iso_of_local_frames_ulift`
(`ModulesGlueIsoOfFrames`).

**Kernel performance discipline** for this section:
1. Use throughout the spellings `ProjTwisting.sheaf (projectiveGrading k N) ((1 : ℕ) : ℤ)`, `ModuleSections.pullback`,
   `projectiveSpaceCoordinate`, verbatim as in `targetFrameIso` / `pullbackFrameIso_section_of_eq`; the chart API is
   keyed by the closed immersion `e.emb`. Only the last step `exact ⟨e, he⟩` converts once to the
   `projectiveSpaceTwist` / `sectionPullbackAlong` / `projectiveSpaceCoordinate` spelling of the target statement
   (this step is not under a projection head, so the kernel only δ-unfolds, which is cheap).
2. All reasoning about "what happens to a section" is done in general lemmas (`twistIsoOn_coordinate`,
   `IsFrame.of_restrictIso_eq_one'`) and only instantiated here; `pullbackFrameIso_section` is instantiated only
   through the `_of_eq` bridge lemma (a direct instantiation is far too slow).
3. Gluing uses `exists_iso_of_local_frames_ulift` with the family of opens passed as the partial application
   `projectivizationChart P`, so that the expected type of `φ` contains no `(fun i => …) i` (which would make the
   kernel unfold the whole pullback sheaf under `restrict`). -/

/-- `x_ℓ ↦ r_{ℓ,ℓ} = 1` is a unit. -/
theorem projectivizationChartEval_X_isUnit {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    IsUnit (projectivizationChartEval (k := k) P ℓ (MvPolynomial.X ℓ)) :=
  projectivizationChartEvalOver_X_isUnit _ P ℓ

/-- The chart morphism `g_ℓ : V_ℓ → D_+(x_ℓ)` (`ProjectiveSpaceOverChart.chartMap`).
`abbrev` of `projectivizationChartMapOver (V ↘ Spec k) P ℓ`. -/
abbrev projectivizationChartMap {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    (projectivizationChart P ℓ).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
        (MvPolynomial.X ℓ)).toScheme :=
  projectivizationChartMapOver (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) P ℓ

/-- `g_ℓ` composed with the open immersion `D_+(x_ℓ) ↪ P^N` is the restriction of `φ` to `V_ℓ`. -/
theorem projectivizationChartMap_comp_ι {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ : Fin (N + 1)) :
    projectivizationChartMap (k := k) P ℓ ≫
        (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ)).ι =
      (projectivizationChart P ℓ).ι ≫ projectivizationMorphism (k := k) M P hP :=
  projectivizationChartMapOver_comp_ι _ M P hP ℓ

/-- `g_ℓ^♯(x_j/x_ℓ) = r_{ℓ,j}` (`x_ℓ ↦ 1`). -/
theorem projectivizationChartMap_appTop_ratioSection {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ j : Fin (N + 1)) :
    (projectivizationChartMap (k := k) P ℓ).appTop
        (ProjectiveSpaceOverChart.ratioSection (R := k) N j ℓ) =
      (projectivizationChart P ℓ).topIso.inv.hom (projectivizationRatio P ℓ j) :=
  projectivizationChartMapOver_appTop_ratioSection _ P ℓ j

/-- `φ^*O(1)|_{V_ℓ} ≅ O_{V_ℓ}`, by pulling back the target frame `x_ℓ` (`pullbackFrameIso` and `targetFrameIso`;
`O(1)` is spelled `ProjTwisting.sheaf … ((1 : ℕ) : ℤ)`, verbatim as in the type of `targetFrameIso`). -/
noncomputable def projectivizationPullbackFrameIso {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ : Fin (N + 1)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphism (k := k) M P hP)).obj
        (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N)
          ((1 : ℕ) : ℤ))).restrict (projectivizationChart P ℓ).ι ≅
      SheafOfModules.unit (R := (projectivizationChart P ℓ).toScheme.ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.pullbackFrameIso (projectivizationMorphism (k := k) M P hP)
    (projectivizationChart P ℓ)
    (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ))
    (projectivizationChartMap (k := k) P ℓ) (projectivizationChartMap_comp_ι (k := k) M P hP ℓ)
    (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N) ((1 : ℕ) : ℤ))
    (ProjectiveSpaceOverChart.targetFrameIso (R := k) N ℓ)

/-- The value of the pulled-back frame on `φ^*x_j|_{V_ℓ}`: `g_ℓ^♯(target frame (x_j))` (the bridge lemma `pullbackFrameIso_section_of_eq`). -/
theorem projectivizationPullbackFrameIso_section {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ j : Fin (N + 1)) :
    (projectivizationPullbackFrameIso (k := k) M P hP ℓ).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection
          ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphism (k := k) M P hP)).obj
            (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N)
              ((1 : ℕ) : ℤ)))
          (projectivizationChart P ℓ)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphism (k := k) M P hP)
            (projectiveSpaceCoordinate k N j))) =
      (projectivizationChartMap (k := k) P ℓ).appTop
        ((ProjectiveSpaceOverChart.targetFrameIso (R := k) N ℓ).hom.app ⊤
          (AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection
            (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N)
              ((1 : ℕ) : ℤ))
            (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ))
            (projectiveSpaceCoordinate k N j))) :=
  AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.pullbackFrameIso_section_of_eq
    (projectivizationMorphism (k := k) M P hP) (projectivizationChart P ℓ)
    (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X ℓ))
    (projectivizationChartMap (k := k) P ℓ) (projectivizationChartMap_comp_ι (k := k) M P hP ℓ)
    (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N) ((1 : ℕ) : ℤ))
    rfl (ProjectiveSpaceOverChart.targetFrameIso (R := k) N ℓ)
    (projectivizationPullbackFrameIso (k := k) M P hP ℓ) rfl
    (projectiveSpaceCoordinate k N j) _ rfl

/-- **Coordinate formula for the pulled-back frame**: `φ^*x_j|_{V_ℓ} ↦ r_{ℓ,j}`. -/
theorem projectivizationPullbackFrameIso_coordinate {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ j : Fin (N + 1)) :
    (projectivizationPullbackFrameIso (k := k) M P hP ℓ).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection
          ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphism (k := k) M P hP)).obj
            (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N)
              ((1 : ℕ) : ℤ)))
          (projectivizationChart P ℓ)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphism (k := k) M P hP)
            (projectiveSpaceCoordinate k N j))) =
      (projectivizationChart P ℓ).topIso.inv.hom (projectivizationRatio P ℓ j) := by
  rw [projectivizationPullbackFrameIso_section]
  -- `targetFrameIso_coordinate` writes `O(1)` as `sheaf 𝒜 (1 : ℤ)`, here it is `sheaf 𝒜 ((1 : ℕ) : ℤ)`;
  -- the difference sits in an argument of the plain def `restrictedGlobalSection` (kernel compares argumentwise, cheap); `erw` goes through.
  erw [AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.targetFrameIso_coordinate]
  exact projectivizationChartMap_appTop_ratioSection (k := k) P ℓ j

/-- `θ_ℓ : φ^*O(1)|_{V_ℓ} ≅ M|_{V_ℓ}`: the pulled-back frame `φ^*x_ℓ` followed by the inverse of the source frame `P_ℓ`. -/
noncomputable def projectivizationTwistIsoOn {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ : Fin (N + 1)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphism (k := k) M P hP)).obj
        (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N)
          ((1 : ℕ) : ℤ))).restrict (projectivizationChart P ℓ).ι ≅
      M.restrict (projectivizationChart P ℓ).ι :=
  projectivizationPullbackFrameIso (k := k) M P hP ℓ ≪≫
    (projectivizationChart_isFrame P ℓ).restrictIso.symm

/-- **`θ_ℓ(φ^*x_j) = P_j`** (`r_{ℓ,j} • P_ℓ = P_j`; an instance of the general lemma `twistIsoOn_coordinate`). -/
theorem projectivizationTwistIsoOn_coordinate {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ j : Fin (N + 1)) :
    (projectivizationTwistIsoOn (k := k) M P hP ℓ).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection
          ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphism (k := k) M P hP)).obj
            (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N)
              ((1 : ℕ) : ℤ)))
          (projectivizationChart P ℓ)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphism (k := k) M P hP)
            (projectiveSpaceCoordinate k N j))) =
      AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection M (projectivizationChart P ℓ)
        (P j) :=
  AlgebraicGeometry.Scheme.Modules.twistIsoOn_coordinate
    (projectivizationPullbackFrameIso (k := k) M P hP ℓ) (projectivizationChart_isFrame P ℓ) _ _ _
    (projectivizationPullbackFrameIso_coordinate (k := k) M P hP ℓ j)
    (by have h := projectivizationRatio_smul P ℓ j
        rwa [AlgebraicGeometry.Scheme.Modules.res_self] at h)

/-- **`φ^*x_ℓ` is a frame of `φ^*O(1)` on `V_ℓ`** (the pulled-back frame sends it to `r_{ℓ,ℓ} = 1`). -/
theorem isFrame_projectivization_pullback_coordinate {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ : Fin (N + 1)) :
    AlgebraicGeometry.Scheme.Modules.IsFrame
      ((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphism (k := k) M P hP)).obj
        (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N) ((1 : ℕ) : ℤ)))
      (projectivizationChart P ℓ)
      (((AlgebraicGeometry.Scheme.Modules.pullback (projectivizationMorphism (k := k) M P hP)).obj
        (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k N)
          ((1 : ℕ) : ℤ))).res le_top
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphism (k := k) M P hP)
          (projectiveSpaceCoordinate k N ℓ))) :=
  AlgebraicGeometry.Scheme.Modules.IsFrame.of_restrictIso_eq_one'
    (projectivizationPullbackFrameIso (k := k) M P hP ℓ) _
    (by have h := projectivizationPullbackFrameIso_coordinate (k := k) M P hP ℓ ℓ
        rwa [projectivizationRatio_self, map_one] at h)

/-- **`φ^*O(1) ≅ M` with `φ^*x_ℓ ↦ P_ℓ`** (step 5; glued along `{V_ℓ}` using frames). -/
theorem projectivizationMorphism_pullback_twist {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    ∃ θ : (AlgebraicGeometry.Scheme.Modules.pullback
        (projectivizationMorphism (k := k) M P hP)).obj (projectiveSpaceTwist k N 1) ≅ M,
      ∀ ℓ, θ.hom.app ⊤
          (sectionPullbackAlong (projectivizationMorphism (k := k) M P hP)
            (projectiveSpaceCoordinate k N ℓ)) = P ℓ := by
  have hcover : (⨆ i : ULift.{u} (Fin (N + 1)), projectivizationChart P i.down) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨i, hi⟩ := hP v
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ULift.up i, hi⟩
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_of_local_frames_ulift
    (projectivizationChart P) hcover
    (fun i => projectivizationTwistIsoOn (k := k) M P hP i.down)
    (fun j => AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (projectivizationMorphism (k := k) M P hP)
      (projectiveSpaceCoordinate k N j))
    P
    (fun i => isFrame_projectivization_pullback_coordinate (k := k) M P hP i)
    (fun i j => projectivizationTwistIsoOn_coordinate (k := k) M P hP i.down j)
  exact ⟨e, he⟩

-- `IsVanishingLocus` lives in `AlgebraicGeometry/Proj/ProjectiveSpace/ProjectiveVanishingLocus`.

/-! ## The chart computation of step 6

`F(P) = 0 ⇒ θ_i(F) = 0` (local formula plus torsion-freeness of tensor powers of a frame), `φ⁻¹D_+(x_i) = V_i`, and
`chartPullback` vanishes on `F/x_i^d`. The general lemmas are in `ProjectivizationChartLocalFormula`. -/

/-- **`F(P) = 0 ⇒ F(r_{i,0},…,r_{i,N}) = 0`** (i.e. `θ_i(F) = 0`, `θ_i = projectivizationChartEval P i`).
Restrict `F(P) = 0` to `V_i` and use the local formula `F(P)|_{V_i} = F(r_i) • P_i^{⊗d}`
(`ProjectivizationChartLocalFormula.res_evalHomogeneousAtSections`, `P_j| = r_{i,j} • P_i|`);
`P_i^{⊗d}` is torsion-free (`eq_zero_of_smul_monomialOn_eq_zero`, `P_i` is a frame on `V_i`), giving `F(r_i) = 0`,
and `F(r_i) = topIso.hom (θ_i F)` (`eval₂_res_eq_topIso_hom`). No case split is needed for `d = 0`. -/
theorem projectivizationChartEval_eq_zero_of_evalHomogeneousAtSections_eq_zero {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    {d : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous d)
    (hzero : evalHomogeneousAtSections M F hF P = 0) (i : Fin (N + 1)) :
    projectivizationChartEval (k := k) P i F = 0 := by
  have hf : ∀ j, M.presheaf.map (homOfLE (le_top : projectivizationChart P i ≤ ⊤)).op (P j) =
      projectivizationRatio P i j •
        M.presheaf.map (homOfLE (le_top : projectivizationChart P i ≤ ⊤)).op (P i) := by
    intro j
    have h := projectivizationRatio_smul P i j
    rw [AlgebraicGeometry.Scheme.Modules.res_self] at h
    exact h.symm
  have hres := ProjectivizationChartLocalFormula.res_evalHomogeneousAtSections M F hF P
    (projectivizationChart P i) _ _ hf
  rw [hzero, map_zero] at hres
  have hcoef := ProjectivizationChartLocalFormula.eq_zero_of_smul_monomialOn_eq_zero M
    (projectivizationChart P i) _ (projectivizationChart_isFrame P i) d (fun _ => 0) _ hres.symm
  rw [ProjectivizationChartLocalFormula.eval₂_res_eq_topIso_hom] at hcoef
  have h2 := congrArg (projectivizationChart P i).topIso.inv hcoef
  rw [Iso.hom_inv_id_apply, map_zero] at h2
  exact h2

/-- **`F(P) = 0 ⇒` the dehomogenization `F/x_i^d` pulls back to zero along the projectivization morphism.**

Write `φ = projectivizationMorphism M P hP : V → P^N`. `chartPullback e Fproj i : (k[x]_{x_i})_0 →+* Γ(φ⁻¹D_+(x_i), O)`
is the ring map induced by the restriction of `φ` over `D_+(x_i)` (`ProjectiveEmbeddingGlobalFactorization.chartPullback`,
which only uses the dimension `N` of `e`), and `embeddingChartLocalizationMap e i F = F/x_i^d`
(`SeedHomogeneousConeFractions.embeddingChartLocalizationMap_homogeneous`).

Proof (the step "if the `F_j` vanish after substitution, the morphism factors through `X`" of Theorem 4.2 of the paper):
1. `φ⁻¹D_+(x_i) = V_i`: `⊇` by `projectivizationChartMap_comp_ι` (`V_i.ι ≫ φ = g_i ≫ D_+(x_i).ι`); `⊆`: for `v ∈ V_ℓ`,
   `P_i|_{V_ℓ} = r_{ℓ,i} • P_ℓ|` (`projectivizationRatio_smul`), and `P_i` is nonvanishing at `v` ⟺ `r_{ℓ,i}(v)` is a
   unit ⟺ `v ∈ D(r_{ℓ,i}) = (V_ℓ.ι ≫ φ)⁻¹D_+(x_i)` (Mathlib `Proj.fromOfGlobalSections_preimage_basicOpen`,
   `θ_ℓ(x_i) = r_{ℓ,i}`); the `{V_ℓ}` cover `V`.
2. Transport `chartPullback` (by definition `(φ.resLE D_+(x_i) (φ⁻¹D_+(x_i))).appTop ∘ topIso⁻¹ ∘ basicOpenIsoAway`)
   along this equality of opens to `V_i`: `φ.resLE D_+(x_i) V_i = g_i` (`cancel_mono` and `resLE_comp_ι`), and the
   `Scheme.homOfLE` between equal opens is an isomorphism with injective `appTop`; it remains to show
   `g_i.appTop (topIso⁻¹ (awayToSection (F/x_i^d))) = 0`.
3. `g_i.appTop (topIso⁻¹ (awayToSection z)) = chartEvaluation θ_i z` (`ProjectiveFactorEquationVanishes.chartMap_appTop_section`),
   `chartEvaluation (F/x_i^d) · θ_i(x_i)^d = θ_i(F)` (`ProjectiveChartEquationEvaluation.chartEvaluation_mk_mul`), and
   `θ_i(x_i) = 1` (`projectivizationChartEval_X_self`).
4. `θ_i(F) = 0`: the local formula `F(P)|_{V_i} = eval₂ (ρ ∘ φ_k) r_i F • P_i^{⊗d}`
   (`ProjectiveFactorEquationVanishes.res_evalHomogeneousAtSections`); `hzero` makes the left-hand side `0`, and
   `P_i^{⊗d}` is a frame of `M^{⊗d}` on `V_i` (tensor powers of a frame are frames), so the coefficient
   `eval₂ (ρ∘φ_k) r_i F = topIso.hom (θ_i F)` is `0`. For `d = 0` (`F` a constant `c`) the formula holds as well. -/
theorem projectivization_chartPullback_localization_eq_zero
    {k : Type u} [Field k] {V X : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N)
    (M : V.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v)
    {d : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous d)
    (hzero : evalHomogeneousAtSections M F hF P = 0) (i : Fin (N + 1)) :
    AlgebraicGeometry.Proj.ProjectiveEmbeddingGlobalFactorization.chartPullback
        (projectivizationMorphism (k := k) M P hP) i
        (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i F) = 0 := by
  have hθ : projectivizationChartEval (k := k) P i F = 0 :=
    projectivizationChartEval_eq_zero_of_evalHomogeneousAtSections_eq_zero M P F hF hzero i
  have hce : ProjectiveSpaceOverChart.chartEvaluation N
      (projectivizationChartEval (k := k) P i) i (projectivizationChartEval_X_isUnit P i)
      (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i F) = 0 := by
    rw [AlgebraicGeometry.Proj.SeedHomogeneousConeFractions.embeddingChartLocalizationMap_homogeneous
      k N i hF]
    exact AlgebraicGeometry.Proj.ProjectiveChartEquationEvaluation.chartEvaluation_mk_eq_zero N _ i _ F d hF hθ
  have key : ∀ (S : V.Opens) (hS : S = projectivizationChart P i)
      (hle : S ≤ projectivizationMorphism (k := k) M P hP ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i)),
      ((projectivizationMorphism (k := k) M P hP).resLE
          (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i))
          S hle).appTop
        ((AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
          (MvPolynomial.X i)).topIso.inv
          (AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i)
            (AlgebraicGeometry.Proj.embeddingChartLocalizationMap k N i F))) = 0 := by
    intro S hS hle
    subst hS
    have hres : (projectivizationMorphism (k := k) M P hP).resLE _ _ hle =
        projectivizationChartMap (k := k) P i := by
      rw [← cancel_mono (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
          (MvPolynomial.X i)).ι,
        AlgebraicGeometry.Scheme.Hom.resLE_comp_ι, projectivizationChartMap_comp_ι]
    rw [hres]
    exact (ProjectivizationChartLocalFormula.chartMap_appTop_section _ N _ i _ _).trans hce
  exact key _ (projectivizationMorphism_preimage_basicOpen (k := k) M P hP i) le_rfl

/-- The chart kernel is contained in the kernel of the pullback: `chartKernelAway i = loc_i(Γ_*(I))`
(`projectiveVanishingIdeal_localizes`), `Γ_*(I) = span F` (`hX`), and each `loc_i(F_j)` is killed by the pullback (previous lemma). -/
private theorem projectivization_chart_kernel_from_vanishing
    {k : Type u} [Field k] {V X : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) {ι : Type u}
    (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    (hX : IsVanishingLocus e F)
    (M : V.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v)
    (hzero : ∀ j, evalHomogeneousAtSections M (F j) (hF j) P = 0) :
    ∀ i : Fin (N + 1),
      AlgebraicGeometry.Proj.ProjectiveEmbedding.chartKernelAway e.emb i ≤
        RingHom.ker (AlgebraicGeometry.Proj.ProjectiveEmbeddingGlobalFactorization.chartPullback
          (projectivizationMorphism (k := k) M P hP) i) := by
  intro i
  have hX' : Ideal.span (Set.range F) = (projectiveVanishingIdeal e.emb.ker).toIdeal := hX
  rw [← projectiveVanishingIdeal_localizes e i, Ideal.map_le_iff_le_comap, ← hX', Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker]
  exact projectivization_chartPullback_localization_eq_zero e M P hP (F j) (hF j) (hzero j) i

theorem projectivizationMorphism_factors {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) {ι : Type u}
    (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    (hX : IsVanishingLocus e F)
    (M : V.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v)
    (hzero : ∀ j, evalHomogeneousAtSections M (F j) (hF j) P = 0) :
    ∃ Φ : V ⟶ X, Φ ≫ e.emb = projectivizationMorphism (k := k) M P hP := by
  have H : ∀ i, AlgebraicGeometry.Proj.ProjectiveEmbedding.chartKernelAway e.emb i ≤
      RingHom.ker (AlgebraicGeometry.Proj.ProjectiveEmbeddingGlobalFactorization.chartPullback
        (projectivizationMorphism (k := k) M P hP) i) :=
    projectivization_chart_kernel_from_vanishing e deg F hF hX M P hP hzero
  obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := AlgebraicGeometry.Proj.ProjectiveEmbeddingGlobalFactorization.existsUnique_factor
    e.emb (projectivizationMorphism (k := k) M P hP) H e.over
    (projectivizationMorphism_comp_over (k := k) M P hP)
  exact ⟨Φ, hΦ⟩

end
