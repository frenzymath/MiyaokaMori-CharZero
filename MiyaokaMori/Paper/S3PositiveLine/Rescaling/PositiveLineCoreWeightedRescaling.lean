import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetChart
import MiyaokaMori.AlgebraicGeometry.Morphisms.AdjoinWeightedRoots
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.AffineLiftGenericPoint
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationInExtension
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCoverFunctionFieldPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveSpacePointOfTupleNaturality
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveRationalPoints

/-! # Shared helpers for the affine lift after finite base change (Lemma 3.1 of the paper)

Small facts used by the assembly of `weighted_rescaling` (`PositiveLineCore`) and by its two
halves `weighted_rescaling_generic_affineJet` (`PositiveLineCoreWeightedRescaling_AffineJet`) and
`weighted_rescaling_jet_of_affineJet` (`BasedJetOfAffineJet`):

* jet charts: `fiberCoords` is natural in the field (`jetChart.fiberCoords_precomp`), depends only on
  the morphism (`jetChart.fiberCoords_congr`), and a `K`-point of `Y_κ^GG` over `V` is determined by
  its image in `C` and its fiber coordinates (`jetChart.hom_ext_of_fiberCoords_eq`);
* the projection of the generic weighted point of a based jet (`BasedJet.genericWeightedPoint_proj`);
* the `k`-algebra structure on `K(C̃)` (`SmoothProjectiveCurve.functionFieldAlgebra`, not an
  instance) and its `Spec` (`SmoothProjectiveCurve.SpecMap_algebraMap_functionFieldAlgebra`);
* a nonzero tuple `b : Fin (n+1) → Fin κ → K(C̃)` of jet coordinates (weight `q + 1` on `b i q`) read
  as a `K(C̃)`-point of `P(w)` on `Spec κ(η_{C̃})` (`jetCoordTuple`, `weightedPointOfCoords`,
  `weightedPointOfCoords_over`), and the invariance of that point under weighted rescaling by a unit
  (`weightedPointOfCoords_scale`, Lemma 3.1 of the paper).

The imports `AdjoinWeightedRoots`, `AffineLiftGenericPoint`, `NormalizationInExtension` and
`PositiveLineCoreWeightedRescalingFunctionField` are not used in this file itself but are kept:
`PositiveLineCoreWeightedRescaling_AffineJet` reaches their declarations through this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- `fiberCoords` is natural in the field: precomposing the `K`-point with
`g : Spec K' ⟶ Spec K` precomposes its fiber coordinates with `g`
(both sides are lifts through the open immersion `π_κ⁻¹(V) ↪ Y_κ^GG`, and lifts are unique). -/
theorem jetChart.fiberCoords_precomp {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {V : C.toScheme.Opens} (chart : jetChart f κ V) {K K' : Type u} [Field K] [Field K']
    (g : AlgebraicGeometry.Spec (CommRingCat.of K') ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (x : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ YGG f κ)
    (hx : Set.range (x ≫ YGG.proj f κ).base ⊆ V)
    (hx' : Set.range ((g ≫ x) ≫ YGG.proj f κ).base ⊆ V) :
    chart.fiberCoords (g ≫ x) hx' = g ≫ chart.fiberCoords x hx := by
  unfold jetChart.fiberCoords
  have hl : AlgebraicGeometry.IsOpenImmersion.lift ((YGG.proj f κ) ⁻¹ᵁ V).ι (g ≫ x)
      (by
        rw [AlgebraicGeometry.Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hx' ⟨y, rfl⟩) =
      g ≫ AlgebraicGeometry.IsOpenImmersion.lift ((YGG.proj f κ) ⁻¹ᵁ V).ι x
      (by
        rw [AlgebraicGeometry.Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hx ⟨y, rfl⟩) := by
    refine (AlgebraicGeometry.IsOpenImmersion.lift_uniq _ _ _ _ ?_).symm
    rw [Category.assoc, AlgebraicGeometry.IsOpenImmersion.lift_fac]
  rw [hl, Category.assoc]

/-- `fiberCoords` depends only on the morphism (eliminates the dependent proof argument). -/
theorem jetChart.fiberCoords_congr {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {V : C.toScheme.Opens} (chart : jetChart f κ V) {K : Type u} [Field K]
    {x y : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ YGG f κ} (h : x = y)
    (hx : Set.range (x ≫ YGG.proj f κ).base ⊆ V)
    (hy : Set.range (y ≫ YGG.proj f κ).base ⊆ V) :
    chart.fiberCoords x hx = chart.fiberCoords y hy := by
  subst h; rfl

/-- Two `K`-points of `Y_κ^GG` lying over `V` with the same image in `C` and the same fiber
coordinates in a jet chart coincide: both factor through `π_κ⁻¹(V) ≅ V ×_k P(w)`, and a morphism
into the fibre product is determined by its two components (`iso_fst` identifies the first with
the image in `V`, and `V.ι` is a monomorphism). -/
theorem jetChart.hom_ext_of_fiberCoords_eq {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {V : C.toScheme.Opens} (chart : jetChart f κ V) {K : Type u} [Field K]
    (x y : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ YGG f κ)
    (hx : Set.range (x ≫ YGG.proj f κ).base ⊆ V)
    (hy : Set.range (y ≫ YGG.proj f κ).base ⊆ V)
    (hproj : x ≫ YGG.proj f κ = y ≫ YGG.proj f κ)
    (hfib : chart.fiberCoords x hx = chart.fiberCoords y hy) :
    x = y := by
  unfold jetChart.fiberCoords at hfib
  set x' := AlgebraicGeometry.IsOpenImmersion.lift ((YGG.proj f κ) ⁻¹ᵁ V).ι x
      (by
        rw [AlgebraicGeometry.Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hx ⟨y, rfl⟩) with hx'
  set y' := AlgebraicGeometry.IsOpenImmersion.lift ((YGG.proj f κ) ⁻¹ᵁ V).ι y
      (by
        rw [AlgebraicGeometry.Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hy ⟨y, rfl⟩) with hy'
  have hxf : x' ≫ ((YGG.proj f κ) ⁻¹ᵁ V).ι = x :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hyf : y' ≫ ((YGG.proj f κ) ⁻¹ᵁ V).ι = y :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  rw [← hxf, ← hyf]
  congr 1
  rw [← cancel_mono chart.iso.hom]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, chart.iso_fst]
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, AlgebraicGeometry.morphismRestrict_ι]
    rw [← Category.assoc, hxf, ← Category.assoc, hyf]
    exact hproj
  · simpa only [Category.assoc] using hfib

/-- The generic weighted point of a based jet lies over `ρ` at the generic point of `C̃`
(`relativeProj.lift_hom`). -/
theorem BasedJet.genericWeightedPoint_proj {f : C.toScheme ⟶ X.toScheme} [MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (hne : ∃ ℓ q, 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) :
    J.genericWeightedPoint hne ≫ YGG.proj f κ =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom :=
  AlgebraicGeometry.Scheme.relativeProj.lift_hom _ _ _ _

/-- The `k`-algebra structure on the function field `K(C̃)` of a smooth projective curve induced by
the structure morphism `C̃ → Spec k` (global functions of `Spec k` → global functions of `C̃` → germ
at the generic point). Same construction as `integralCurve_functionField_algebra`
for integral curves. **Not** an instance; users write `letI := Ct.functionFieldAlgebra`. -/
@[instance_reducible] noncomputable def SmoothProjectiveCurve.functionFieldAlgebra (Ct : SmoothProjectiveCurve k) :
    Algebra k Ct.toScheme.functionField :=
  ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Ct.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
    Ct.toScheme.presheaf.germ ⊤ (genericPoint Ct.toScheme) (by simp)).hom.toAlgebra

/-- A family of jet coordinates `b i q` (weight `q + 1`), not all zero, as a nonzero point of
`K^{σ}` for the index set `σ = ULift (Fin (n+1) × Fin κ)` of `jetWeights n κ`. -/
def jetCoordTuple {K : Type u} [Field K] {n κ : ℕ} (b : Fin (n + 1) → Fin κ → K)
    (hne : ∃ i q, b i q ≠ 0) : {v : ULift.{u} (Fin (n + 1) × Fin κ) → K // v ≠ 0} :=
  ⟨fun p => b p.down.1 p.down.2, fun h => by
    obtain ⟨i, q, hiq⟩ := hne
    exact hiq (congrFun h ⟨(i, q)⟩)⟩

/-- The weighted point of a nonzero tuple `b` of rational functions on `C̃`: the `K(C̃)`-point
`pointOfTuple b : Spec K(C̃) ⟶ P(jetWeights n κ)` (weights `q + 1` on `b i q`), read on
`Spec κ(η_C̃)` through `K(C̃) ≅ κ(η_C̃)` so that it can be compared with the fiber coordinates
(`jetChart.fiberCoords`) of a morphism `Spec κ(η_C̃) → Y_κ^GG`. The `k`-algebra structure on
`K(C̃)` is `SmoothProjectiveCurve.functionFieldAlgebra`. -/
noncomputable def weightedPointOfCoords (Ct : SmoothProjectiveCurve k) (n κ : ℕ)
    (b : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, b i q ≠ 0) :
    AlgebraicGeometry.Spec (Ct.toScheme.residueField (genericPoint Ct.toScheme)) ⟶
      weightedProjectiveSpace k (jetWeights.{u} n κ) (jetWeights_pos _ _) :=
  letI := Ct.functionFieldAlgebra
  haveI : AlgebraicGeometry.IsIntegral Ct.toScheme := Ct.isIntegral
  AlgebraicGeometry.Spec.map Ct.toScheme.functionFieldIsoResidueField.hom ≫
    weightedProjectiveSpace.pointOfTuple k (jetWeights.{u} n κ) (jetWeights_pos _ _)
      Ct.toScheme.functionField (jetCoordTuple b hne)

/-- `Spec` of the `k`-algebra structure map of `K(C̃)` is `Spec K(C̃) → C̃ → Spec k`
(`fromSpecStalk_toSpecΓ`, `toSpecΓ_naturality`, `toSpecΓ_SpecMap_ΓSpecIso_inv`). -/
theorem SmoothProjectiveCurve.SpecMap_algebraMap_functionFieldAlgebra (Ct : SmoothProjectiveCurve k) :
    letI := Ct.functionFieldAlgebra
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k Ct.toScheme.functionField)) =
      Ct.toScheme.fromSpecStalk (genericPoint Ct.toScheme) ≫
        (Ct.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  change AlgebraicGeometry.Spec.map ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Ct.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
    Ct.toScheme.presheaf.germ ⊤ (genericPoint Ct.toScheme) (by simp)) = _
  rw [AlgebraicGeometry.Spec.map_comp, AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← AlgebraicGeometry.Scheme.toSpecΓ_naturality_assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The weighted point of a tuple is a `k`-morphism whose structure map is that of
`Spec κ(η_C̃) → C̃ → Spec k`; the analogue of `jetChart.fiberCoords_over`, so that the two sides of
`weighted_rescaling_generic_tuple` are `KPoint`s for the same `k`-algebra structure. -/
theorem weightedPointOfCoords_over (Ct : SmoothProjectiveCurve k) (n κ : ℕ)
    (b : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, b i q ≠ 0) :
    weightedPointOfCoords Ct n κ b hne ≫
        (weightedProjectiveSpace k (jetWeights.{u} n κ) (jetWeights_pos _ _)
          ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = Ct.toScheme.fromSpecResidueField (genericPoint Ct.toScheme) ≫
          (Ct.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  letI := Ct.functionFieldAlgebra
  haveI : AlgebraicGeometry.IsIntegral Ct.toScheme := Ct.isIntegral
  unfold weightedPointOfCoords
  rw [Category.assoc, weightedProjectiveSpace.pointOfTuple_over,
    Ct.SpecMap_algebraMap_functionFieldAlgebra, ← Category.assoc]
  rfl

/-- **Weighted rescaling does not change the weighted point** (Lemma 3.1 of the paper: "the tuple
`a_α` is a weighted rescaling of `b_α`"): if `b' i q = γ^{q+1} · b i q` for a nonzero rational
function `γ`, then `weightedPointOfCoords b' = weightedPointOfCoords b`
(`weightedProjectiveSpace.kPointOfTuple_congr`, , with the
unit `γ` of the `scalingSetoid`; `jetWeights ⟨(i,q)⟩ = q + 1`). -/
theorem weightedPointOfCoords_scale (Ct : SmoothProjectiveCurve k) (n κ : ℕ)
    (b b' : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, b i q ≠ 0)
    (hne' : ∃ i q, b' i q ≠ 0) (γ : Ct.toScheme.functionField) (hγ : γ ≠ 0)
    (hb' : ∀ i q, b' i q = γ ^ ((q : ℕ) + 1) * b i q) :
    weightedPointOfCoords Ct n κ b' hne' = weightedPointOfCoords Ct n κ b hne := by
  letI := Ct.functionFieldAlgebra
  have : AlgebraicGeometry.IsIntegral Ct.toScheme := Ct.isIntegral
  -- the two tuples are related by the weighted scaling by the unit `γ`
  have h := weightedProjectiveSpace.kPointOfTuple_congr k (jetWeights.{u} n κ) (jetWeights_pos _ _)
    Ct.toScheme.functionField (jetCoordTuple b hne) (jetCoordTuple b' hne')
    ⟨Units.mk0 γ hγ, fun p => hb' p.down.1 p.down.2⟩
  have h' : weightedProjectiveSpace.pointOfTuple k (jetWeights.{u} n κ) (jetWeights_pos _ _)
        Ct.toScheme.functionField (jetCoordTuple b' hne') =
      weightedProjectiveSpace.pointOfTuple k (jetWeights.{u} n κ) (jetWeights_pos _ _)
        Ct.toScheme.functionField (jetCoordTuple b hne) :=
    (congrArg Subtype.val h).symm
  exact congrArg
    (fun z => AlgebraicGeometry.Spec.map Ct.toScheme.functionFieldIsoResidueField.hom ≫ z) h'

end
