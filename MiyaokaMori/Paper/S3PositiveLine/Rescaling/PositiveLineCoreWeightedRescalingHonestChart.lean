import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetChart

/-! # Honest jet charts

A `jetChart f κ V` (`JetChart`) is a pair `(coords, iso)` with `iso : π_κ⁻¹(V) ≅ V ×_k P(w)`
compatible with the projection to `V` (`iso_fst`) — and **nothing** ties `iso` to `coords` or to the
jet algebra. `jetChart.exists_mem` fills `coords` with `0` and takes `iso` from
`relativeProj_locallyWeighted_exists_affine_chart`. Reading "fiber coordinates" in such a chart (`jetChart.fiberCoords`) is
therefore only meaningful when the chart is *honest*: `iso` is the isomorphism induced on relative
`Proj` by a weighted-polynomial presentation `S(V) ≅ Γ(V)[x_{i,q}]` of the jet algebra in which the
`coords` are the variables. This file makes that notion precise (`jetChart.IsHonest`), bundles it
(`HonestJetChart`), and proves the existence of honest charts around every point
(`HonestJetChart.exists_mem`). Ingredients of the existence proof:
`relativeProj_locallyWeighted_exists_honest_chart` (this file: the three squares (A) `projChart_isPullback`,
(B) `projIso`, (C) `weightedProj_baseChange_isPullback` of `relativeProj_locallyWeighted_chart`, rebuilt
with the second component recorded as `Proj.map (WeightedPolynomialAtlas.baseGradedHom)`),
`SmoothProjectiveCurve.ofHom_opensAlgebraMap` (`opensAlgebraMap = AffineZariskiSite.baseRingHom`, by
`Spec` full faithfulness), and `jetAlgebra_isLocallyWeightedPolynomial` (stated in `JetChart`).

Why honesty is needed: for an
arbitrary `jetChart` value the conclusion of the paper's second paragraph ("the based jet built from
the tuple `b` has generic weighted point with fiber coordinate `[b]`") quantifies over isomorphisms
`π_κ⁻¹(V) ≅ V ×_k P(w)` over `V` that need not be induced by graded-algebra isomorphisms; twisting an
honest `iso` by an automorphism of `V ×_k P(w)` over `V` that does not lift to the weighted
projective *stack* (for `(n, κ) = (0, 2)`: `P(1,2) ≅ P¹` and, e.g., `[x₁ : x₂] ↦ [x₁ : x₂ + x₁²]`
composed with a non-graded automorphism of `P¹`) sends points whose honest coordinates are
`(1, u)` with `u` a square to points whose honest coordinates `(1, u/(1 ± u))` have odd order at some
point of `C̃` — no based jet with nowhere-zero normalized tuple has such a generic weighted point
(the weighted order `min ord_y(b_{i,q})/(q+1)` of a based jet is the integer `w_y`). So the lemma must
assume honesty; the paper never considers non-honest charts (Lemma 3.1 of the paper: "in its
coordinates").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- The `k`-algebra structure map `k → Γ(C, V)` of an open `V` of the `k`-curve `C`
(global functions of `Spec k` → functions on `V` through the structure morphism). -/
def SmoothProjectiveCurve.opensAlgebraMap (C : SmoothProjectiveCurve k) (V : C.toScheme.Opens) :
    k →+* Γ(C.toScheme, V) :=
  (((C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ V le_top).hom).comp
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- An affine open `V` of `C` as an object of the small affine Zariski site (the index type of the
charts of `GradedAffineAlgebra.relativeProj`). -/
abbrev SmoothProjectiveCurve.affineSite (C : SmoothProjectiveCurve k) {V : C.toScheme.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) : C.toScheme.AffineZariskiSite := ⟨V, hV⟩

/-- The `Proj`-chart `Proj (S(V)) → Y_κ^GG` of the affine open `V`
(`GradedAffineAlgebra.projChart`; an open immersion with image `π_κ⁻¹(V)`), as a morphism into
`π_κ⁻¹(V)`: it lands there because `projChart ≫ π_κ = projToOpen ≫ V.ι` (`projChart_hom`). -/
def jetProjChartToPreimage (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) {V : C.toScheme.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) :
    AlgebraicGeometry.Proj ((jetAlgebra f κ).toGradedAffineAlgebra.grading (C.affineSite hV)) ⟶
      ((YGG.proj f κ) ⁻¹ᵁ V).toScheme :=
  AlgebraicGeometry.IsOpenImmersion.lift ((YGG.proj f κ) ⁻¹ᵁ V).ι
    ((jetAlgebra f κ).toGradedAffineAlgebra.projChart (C.affineSite hV)) (by
      rw [AlgebraicGeometry.Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      have h : (YGG.proj f κ).base (((jetAlgebra f κ).toGradedAffineAlgebra.projChart (C.affineSite hV)).base y) =
          ((C.affineSite hV).toOpens.ι).base
            (((jetAlgebra f κ).toGradedAffineAlgebra.projToOpen (C.affineSite hV)).base y) :=
        congrArg (fun m => m.base y) ((jetAlgebra f κ).toGradedAffineAlgebra.projChart_hom (C.affineSite hV))
      show (YGG.proj f κ).base (((jetAlgebra f κ).toGradedAffineAlgebra.projChart (C.affineSite hV)).base y) ∈ V
      rw [h]
      exact (((jetAlgebra f κ).toGradedAffineAlgebra.projToOpen (C.affineSite hV)).base y).2)

/-- `jetProjChartToPreimage` followed by the inclusion `π_κ⁻¹(V) ↪ Y_κ^GG` is the `Proj`-chart
`projChart` (defining property of `IsOpenImmersion.lift`). -/
theorem jetProjChartToPreimage_ι (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) :
    jetProjChartToPreimage f κ hV ≫ ((YGG.proj f κ) ⁻¹ᵁ V).ι =
      (jetAlgebra f κ).toGradedAffineAlgebra.projChart (C.affineSite hV) :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _

/-- **Honesty of a jet chart** (§2.1 of the paper, Lemma 3.1 of the paper): the chart's
`iso : π_κ⁻¹(V) ≅ V ×_k P(w)` is the isomorphism of relative `Proj` induced by a weighted-polynomial
presentation of the jet algebra on `V`. Precisely, writing `S := jetAlgebra f κ`,
`A := S.toGradedAffineAlgebra`, `U := ⟨V, hV⟩`, `w := jetWeights n κ` and `𝒜 := k[x_σ]` with its
weighted grading, there are

* a ring isomorphism `ε : S(V) ≃+* Γ(C, V)[x_σ]` identifying the `m`-th graded piece of `S(V)` with
  the weighted-homogeneous polynomials of weight `m`, the structure map `Γ(C,V) → S(V)` with the
  constants, and the chart coordinates `coords p ∈ S_{w p}(V)` (put into `S(V)` by `ofPiece`) with
  the variables `x_p` — i.e. `ε` is a chart of a `WeightedPolynomialAtlas` whose variables are the
  `coords`;
* the graded ring homomorphism `φ : 𝒜 → A.grading U` obtained from `ε⁻¹` by restricting the
  coefficients to `k` (`φ = ε⁻¹ ∘ MvPolynomial.map (k → Γ(C,V))`), with the irrelevant-ideal
  condition `hφ` needed for `Proj.map`;

such that the second component of `iso` on the `Proj`-chart `Proj (A.grading U) → π_κ⁻¹(V)`
(`jetProjChartToPreimage`, i.e. `GradedAffineAlgebra.projChart` — an open immersion with image
`π_κ⁻¹(V)` — lifted into `π_κ⁻¹(V)`) is `Proj.map φ hφ`, i.e. "read the coordinates `coords` and
forget the base": `jetProjChartToPreimage ≫ iso.hom ≫ pullback.snd = Proj.map φ hφ`. (The first component is fixed by
`iso_fst`.) For such a chart, `jetChart.fiberCoords x` of a `K`-point `x` given by
`relativeProj.lift` data is `pointOfTuple` of the values of the `coords` on that data — the fact
that  step 6 needs. -/
def jetChart.IsHonest {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ} {V : C.toScheme.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (chart : jetChart f κ V) : Prop :=
  let U : C.toScheme.AffineZariskiSite := C.affineSite hV
  let A : C.toScheme.GradedAffineAlgebra := (jetAlgebra f κ).toGradedAffineAlgebra
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (jetWeights.{u} X.toVariety.dim κ)
  ∃ (ε : (jetAlgebra f κ).sectionsRing V ≃+*
        MvPolynomial (ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ)) Γ(C.toScheme, V))
    (φ : MvPolynomial.weightedHomogeneousSubmodule k (jetWeights.{u} X.toVariety.dim κ) →+*ᵍ
        A.grading U)
    (hφ : HomogeneousIdeal.irrelevant (A.grading U) ≤
        (HomogeneousIdeal.irrelevant
          (MvPolynomial.weightedHomogeneousSubmodule k (jetWeights.{u} X.toVariety.dim κ))).map φ),
    (∀ (m : ℕ) (a : (jetAlgebra f κ).sectionsRing V),
        a ∈ A.grading U m ↔ (ε a).IsWeightedHomogeneous (jetWeights.{u} X.toVariety.dim κ) m) ∧
    (∀ r : Γ(C.toScheme, V), ε ((jetAlgebra f κ).sectionsUnitHom V r) = MvPolynomial.C r) ∧
    (∀ p : Fin (X.toVariety.dim + 1) × Fin κ,
        ε ((jetAlgebra f κ).ofPiece V (jetWeights.{u} X.toVariety.dim κ ⟨p⟩) (chart.coords p)) =
          MvPolynomial.X ⟨p⟩) ∧
    (∀ x : MvPolynomial (ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ)) k,
        φ x = ε.symm (MvPolynomial.map (C.opensAlgebraMap V) x)) ∧
    jetProjChartToPreimage f κ hV ≫ chart.iso.hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
      AlgebraicGeometry.Proj.map φ hφ

/-- An honest jet chart on an affine open `V` (`jetChart.IsHonest`), bundled so that a statement
producing or consuming one keeps the arity of the corresponding statement about `jetChart`
(`chart.fiberCoords`, `chart.iso`, … resolve through the parent projection `tojetChart`). -/
structure HonestJetChart (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (V : C.toScheme.Opens)
    extends jetChart f κ V where
  isAffineOpen : AlgebraicGeometry.IsAffineOpen V
  honest : jetChart.IsHonest isAffineOpen ⟨coords, iso, iso_fst⟩

/-! ## The generic honest chart of a weighted-polynomial atlas

`relativeProj_locallyWeighted_chart` (`LocallyWeightedProjLocalProduct`) builds
`π⁻¹(U_i) ≅ U_i ×_k P(w)` as the composite of three squares (A) `projChart_isPullback`, (B) `projIso`,
(C) `weightedProj_baseChange_isPullback`, but its statement only exposes the first component and the
twists. Here the same composite is rebuilt with its **second component** recorded: on the `Proj`-chart
it is `Proj.map` of `ε_i⁻¹ ∘ (k → Γ(U_i))` (`WeightedPolynomialAtlas.baseGradedHom`). -/

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} {S : X.GradedAffineAlgebra} {σ : Type u} {w : σ → ℕ}

/-- The graded ring homomorphism `k[x_σ]_w → S(U_i)`, `p ↦ ε_i⁻¹ (p with coefficients pushed along
`k → Γ(X, U_i)`)`: the composite of the base change `weightedMapGraded` along
`AffineZariskiSite.baseRingHom pX U_i` and the inverse atlas chart `gradedSymm`. -/
def baseGradedHom (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    MvPolynomial.weightedHomogeneousSubmodule k w →+*ᵍ S.grading (𝒜.chart i) :=
  (𝒜.gradedSymm i).comp
    (MvPolynomial.weightedMapGraded w (AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom)

theorem baseGradedHom_apply (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) (p : MvPolynomial σ k) :
    𝒜.baseGradedHom pX i p =
      (𝒜.equiv i).symm
        (MvPolynomial.map (AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom p) := rfl

/-- `baseGradedHom` satisfies the irrelevant-ideal hypothesis of `Proj.map` (both factors do). -/
theorem baseGradedHom_irrelevant_le (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    HomogeneousIdeal.irrelevant (S.grading (𝒜.chart i)) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule k w)).map
        (𝒜.baseGradedHom pX i) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (MvPolynomial.weightedMapGraded_irrelevant_le w _) (𝒜.gradedSymm_irrelevant_le i)

end AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

section GenericHonestChart

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- **Honest affine chart of the relative `Proj` of a locally weighted polynomial algebra**
(§2.1 of the paper; Lemma 3.1 of the paper; Stacks 01NQ + 01N2). For a chart `U_i` of
the atlas `𝒜` of `S`, there is `e : π⁻¹(U_i) ≅ U_i ×_k P_k(w)` over `U_i` (first component `π ∣_ U_i`)
whose second component, read on the `Proj`-chart `Proj S(U_i) → π⁻¹(U_i)` (any `g` lifting
`projChart U_i` through `π⁻¹(U_i) ↪ Proj_X S`), is `Proj.map (baseGradedHom pX 𝒜 i)`.

Proof: `e := (pullbackRestrictIsoRestrict π U_i)⁻¹ ≫ eA⁻¹ ≫ projIso i ≫ eC` with (A) `eA : Proj S(U_i) ≅
π ×_X U_i` from `projChart_isPullback` (components `projChart`, `projToOpen`), (B) `projIso i =
Proj.map (gradedSymm i)`, (C) `eC : Proj Γ(U_i)[x]_w ≅ U_i ×_k P(w)` from
`weightedProj_baseChange_isPullback` (second component `Proj.map (weightedMapGraded (baseRingHom))`).
`g ≫ (pullbackRestrictIsoRestrict π U_i)⁻¹ = eA.hom` by comparing both components
(`pullbackRestrictIsoRestrict_inv_fst`, `morphismRestrict_ι`, `projChart_hom`), so the second component
on the chart is `Proj.map (gradedSymm) ≫ Proj.map (weightedMapGraded _) = Proj.map (comp)`
(`Proj.map_comp`). -/
theorem relativeProj_locallyWeighted_exists_honest_chart {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (S : X.GradedQCAlgebra) {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    ∃ e : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ (𝒜.chart i).toOpens).toScheme ≅
        CategoryTheory.Limits.pullback ((𝒜.chart i).toOpens.ι ≫ pX)
          (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)),
      e.hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
          (AlgebraicGeometry.Scheme.relativeProj S).hom ∣_ (𝒜.chart i).toOpens ∧
        ∀ g : AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (𝒜.chart i)) ⟶
            ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ (𝒜.chart i).toOpens).toScheme,
          g ≫ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ (𝒜.chart i).toOpens).ι =
              S.toGradedAffineAlgebra.projChart (𝒜.chart i) →
          g ≫ e.hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
            AlgebraicGeometry.Proj.map (𝒜.baseGradedHom pX i) (𝒜.baseGradedHom_irrelevant_le pX i) := by
  classical
  -- (A) the chart square of the relative Proj is a pullback (Stacks 01NQ)
  obtain ⟨eA, hA1, hA2⟩ : ∃ eA : AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (𝒜.chart i)) ≅
      CategoryTheory.Limits.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom
        (𝒜.chart i).toOpens.ι,
      eA.hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
          S.toGradedAffineAlgebra.projChart (𝒜.chart i) ∧
        eA.hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
          S.toGradedAffineAlgebra.projToOpen (𝒜.chart i) := by
    have hA := (S.toGradedAffineAlgebra.projChart_isPullback (𝒜.chart i)).flip
    exact ⟨hA.isoPullback, hA.isoPullback_hom_fst, hA.isoPullback_hom_snd⟩
  -- (C) Proj of the weighted polynomial ring over Γ(X,U) is the base change of P_k(w)
  obtain ⟨eC, hC1, hC2⟩ : ∃ eC : AlgebraicGeometry.Proj
      (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w) ≅
      CategoryTheory.Limits.pullback ((𝒜.chart i).toOpens.ι ≫ pX)
        (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)),
      eC.hom ≫ CategoryTheory.Limits.pullback.fst _ _ = 𝒜.weightedProjToOpen i ∧
        eC.hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
          AlgebraicGeometry.Proj.map (MvPolynomial.weightedMapGraded w
              (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom)
            (MvPolynomial.weightedMapGraded_irrelevant_le w
              (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom) := by
    have hC0 := weightedProj_baseChange_isPullback k w hw Γ(X, (𝒜.chart i).toOpens)
      (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i))
    have hC1 : CategoryTheory.IsPullback
        (AlgebraicGeometry.Proj.map (MvPolynomial.weightedMapGraded w
            (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom)
          (MvPolynomial.weightedMapGraded_irrelevant_le w
            (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom))
        (𝒜.weightedProjToOpen i)
        (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((𝒜.chart i).toOpens.ι ≫ pX) :=
      hC0.of_iso' (Iso.refl _) (Iso.refl _) (𝒜.chart i).2.isoSpec (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        (by
          simp only [Iso.refl_hom, Category.id_comp,
            AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas.weightedProjToOpen,
            Category.assoc, Iso.inv_hom_id, Category.comp_id])
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        (by
          rw [Iso.refl_hom, Category.comp_id]
          exact AlgebraicGeometry.Scheme.AffineZariskiSite.isoSpec_hom_Spec_map_baseRingHom pX _)
    have hC := hC1.flip
    exact ⟨hC.isoPullback, hC.isoPullback_hom_fst, hC.isoPullback_hom_snd⟩
  -- (B) the atlas identifies the chart's Proj with the weighted polynomial Proj; assemble
  refine ⟨(AlgebraicGeometry.pullbackRestrictIsoRestrict (AlgebraicGeometry.Scheme.relativeProj S).hom
      (𝒜.chart i).toOpens).symm ≪≫ (eA.symm ≪≫ 𝒜.projIso i ≪≫ eC), ?_, ?_⟩
  · have hfst : (eA.symm ≪≫ 𝒜.projIso i ≪≫ eC).hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
        CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.relativeProj S).hom
          ((𝒜.chart i).toOpens.ι) := by
      rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc, hC1,
        AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas.projIso_hom_weightedProjToOpen,
        Iso.inv_comp_eq, hA2]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfst,
      ← AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict, Iso.inv_hom_id_assoc]
  · intro g hg
    have hg' : g ≫ (AlgebraicGeometry.pullbackRestrictIsoRestrict
        (AlgebraicGeometry.Scheme.relativeProj S).hom (𝒜.chart i).toOpens).inv = eA.hom := by
      apply CategoryTheory.Limits.pullback.hom_ext
      · rw [Category.assoc, AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst, hg, hA1]
      · rw [Category.assoc, hA2]
        change g ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom ∣_ (𝒜.chart i).toOpens =
          S.toGradedAffineAlgebra.projToOpen (𝒜.chart i)
        rw [← cancel_mono (𝒜.chart i).toOpens.ι, Category.assoc,
          AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc, hg]
        exact S.toGradedAffineAlgebra.projChart_hom (𝒜.chart i)
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, reassoc_of% hg', Iso.trans_hom, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, Category.assoc, hC2, Iso.hom_inv_id_assoc,
      AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas.projIso_hom]
    exact (AlgebraicGeometry.Proj.map_comp _ _ (MvPolynomial.weightedMapGraded_irrelevant_le w _)
      (𝒜.gradedSymm_irrelevant_le i)).symm

end GenericHonestChart

/-- `opensAlgebraMap` agrees with the ring map `baseRingHom` of `LocallyWeightedProjLocalProduct`
(`Spec` is fully faithful: both correspond to `V ≅ Spec Γ(V) → C → Spec k`;
`Scheme.Opens.toSpecΓ_SpecMap_appLE` identifies `Spec.map (appLE)` with `resLE`). -/
theorem SmoothProjectiveCurve.ofHom_opensAlgebraMap (C : SmoothProjectiveCurve k) {V : C.toScheme.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) :
    CommRingCat.ofHom (C.opensAlgebraMap V) =
      AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (C.affineSite hV) := by
  show CommRingCat.ofHom (C.opensAlgebraMap V) = AlgebraicGeometry.Spec.preimage
    (hV.isoSpec.inv ≫ V.ι ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  rw [← AlgebraicGeometry.Spec.preimage_map (CommRingCat.ofHom (C.opensAlgebraMap V))]
  congr 1
  rw [Iso.eq_inv_comp, AlgebraicGeometry.IsAffineOpen.isoSpec_hom]
  have h : CommRingCat.ofHom (C.opensAlgebraMap V) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ V le_top := rfl
  have key : V.toSpecΓ ≫ AlgebraicGeometry.Spec.map
      ((C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appLE ⊤ V le_top) =
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).resLE ⊤ V le_top ≫
        (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of k)).Opens).toSpecΓ :=
    AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE _ _ _ _
  rw [h, AlgebraicGeometry.Spec.map_comp, ← Category.assoc, key, Category.assoc,
    AlgebraicGeometry.Scheme.Opens.toSpecΓ_top, Category.assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  exact AlgebraicGeometry.Scheme.Hom.resLE_comp_ι _ _

/- `jetAlgebra_isLocallyWeightedPolynomial` (the `hloc` block of `jetChart.exists_mem`) is stated in `JetChart`. -/

/-- **Every point of `C` lies in the base of an honest jet chart** (§2 of the paper; Lemma 3.1
of the paper). This is `jetChart.exists_mem` with the chart made honest.

Proof (the Lean follows it step by step):
1. `S := jetAlgebra f κ` is locally a weighted polynomial algebra with weights `jetWeights n κ`
   (`jetGradedAlgebra_isLocallyWeightedPolynomial`, ;
   the ~50-line derivation of its hypotheses from `MMSetup` is the block `hloc` in the proof of
   `jetChart.exists_mem` — copy it). By `isLocallyWeightedPolynomial_iff` this is a
   `WeightedPolynomialAtlas` `𝒜` of `S.toGradedAffineAlgebra`: affine opens `U_i` covering `C` and
   ring isomorphisms `ε_i : S(U_i) ≃+* Γ(U_i)[x_σ]` matching the gradings (`equiv_grading`) and the
   structure maps (`equiv_unit`). Take `i` with `c ∈ U_i` (`covers`) and `V := U_i`, `ε := ε_i`.
2. `coords p := component of ε⁻¹(x_p) in degree w p` (`ε⁻¹(x_p) ∈ grading (w p)` by `symm_mem`
   since `x_p` is weighted homogeneous of weight `w p`; `sectionsPieceEquivGrading` turns it into a
   section of `S_{w p}` over `V`, and `ofPiece` of it is `ε⁻¹(x_p)` again by
   `coe_sectionsPieceEquivGrading`), so `ε (ofPiece (coords p)) = x_p`.
3. `φ := ε⁻¹ ∘ MvPolynomial.map (k → Γ(V))` is a graded ring homomorphism `k[x_σ] → A.grading U`
   (`MvPolynomial.map` preserves weighted homogeneity: `IsWeightedHomogeneous.map`; then
   `equiv_grading`), and satisfies the irrelevant-ideal condition of `Proj.map`: every weighted
   homogeneous element of positive weight of `S(V)` is `ε⁻¹` of a polynomial with no constant term,
   hence in the ideal generated by the `φ(x_p)` (in fact `A.grading U` is generated over its degree
   `0` part `Γ(V)` by the `φ(x_p)`).
4. `Proj.map φ hφ : Proj (A.grading U) ⟶ P(w)` together with the structure morphism
   `projToOpen U : Proj (A.grading U) ⟶ V` gives a morphism to `V ×_k P(w)`; it is an isomorphism
   because `Proj (A.grading U) = Proj (Γ(V)[x_σ]) = Proj (k[x_σ] ⊗_k Γ(V))` is the base change of
   `P(w)` to `V` (Stacks 01MX/01O3 for the affine base `V`:
   `relativeProj_weightedPolynomialQCAlgebra_spec_iso` gives `Proj_V (Γ(V)[x]) ≅ V ×_k P(w)`; its
   second component is `Proj.map` of the coefficient inclusion by construction). Transport along
   the open immersion `projChart U : Proj (A.grading U) ⟶ π_κ⁻¹(V)` (an isomorphism onto
   `π_κ⁻¹(V)`: `projChart_isPullback`, `proj_preimage_eq_opensRange`) to get
   `iso : π_κ⁻¹(V) ≅ V ×_k P(w)`; `iso_fst` is `projChart_hom` (the first component is
   `projToOpen U ≫ V.ι = projChart ≫ π_κ`, i.e. `π_κ ∣_ V`), and the honesty equation is the
   definition of `iso` on the chart. ∎

Steps 1–3 are `jetAlgebra_isLocallyWeightedPolynomial`, `WeightedPolynomialAtlas.symm_mem` +
`sectionsPieceEquivGrading`, and `WeightedPolynomialAtlas.baseGradedHom` (+ `ofHom_opensAlgebraMap`
to identify `baseRingHom` with `opensAlgebraMap`); step 4 is
`relativeProj_locallyWeighted_exists_honest_chart` (no need for
`relativeProj_weightedPolynomialQCAlgebra_spec_iso`: square (C) is Mathlib's base change of `Proj`,
Stacks 01N2, as in `relativeProj_locallyWeighted_chart`). Edge case `κ = 0` — `σ` is empty,
`S = O_C`, `P(w) = Proj k = ∅`, `Y_0^GG = ∅`: nothing special happens in the proof. -/
theorem HonestJetChart.exists_mem (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    (c : C.toScheme) :
    ∃ V : C.toScheme.Opens, AlgebraicGeometry.IsAffineOpen V ∧ c ∈ V ∧
      Nonempty (HonestJetChart f κ V) := by
  obtain ⟨𝒜⟩ := jetAlgebra_isLocallyWeightedPolynomial f κ
  obtain ⟨i, hi⟩ := 𝒜.covers c
  obtain ⟨e, he1, he2⟩ := relativeProj_locallyWeighted_exists_honest_chart
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetAlgebra f κ)
    (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _) 𝒜 i
  refine ⟨(𝒜.chart i).toOpens, (𝒜.chart i).2, hi, ⟨?_⟩⟩
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (jetWeights.{u} X.toVariety.dim κ)
  refine
    { coords := fun p => ((jetAlgebra f κ).sectionsPieceEquivGrading (𝒜.chart i).toOpens
        (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)).symm
        ⟨(𝒜.equiv i).symm (MvPolynomial.X ⟨p⟩),
          𝒜.symm_mem i (MvPolynomial.isWeightedHomogeneous_X _ _ _)⟩
      iso := e
      iso_fst := he1
      isAffineOpen := (𝒜.chart i).2
      honest := ?_ }
  refine ⟨𝒜.equiv i, 𝒜.baseGradedHom (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) i,
    𝒜.baseGradedHom_irrelevant_le _ i, 𝒜.equiv_grading i, 𝒜.equiv_unit i, ?_, ?_,
    he2 (jetProjChartToPreimage f κ (𝒜.chart i).2) (jetProjChartToPreimage_ι f κ (𝒜.chart i).2)⟩
  · intro p
    rw [← AlgebraicGeometry.Scheme.GradedQCAlgebra.coe_sectionsPieceEquivGrading,
      AddEquiv.apply_symm_apply]
    exact RingEquiv.apply_symm_apply _ _
  · intro x
    have hb : (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (𝒜.chart i)).hom =
        C.opensAlgebraMap (𝒜.chart i).toOpens :=
      congrArg CommRingCat.Hom.hom
        (SmoothProjectiveCurve.ofHom_opensAlgebraMap C (𝒜.chart i).2).symm
    show (𝒜.equiv i).symm (MvPolynomial.map (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (𝒜.chart i)).hom x) = _
    exact congrArg (fun ψ : k →+* Γ(C.toScheme, (𝒜.chart i).toOpens) =>
      (𝒜.equiv i).symm (MvPolynomial.map ψ x)) hb

end
