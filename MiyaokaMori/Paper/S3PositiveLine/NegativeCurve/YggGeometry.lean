import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothRelativeDimensionOfDim
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConePunctured
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetAlgebraLocallyWeightedPolynomial
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverIffProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionOfSeparatedIsClosedImmersion
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGenerationMultiple
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjNormal
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjProperLocal

/-! # Ygg geometry

Public geometric facts about the paper's `Y_κ^GG = Proj_C S` (`YGG f κ`), for a
map `f : C → X` with `MMSetup f` and `n := dim X`:
* `YGG.jetAlgebra_isLocallyWeightedPolynomial`: `S = jetAlgebra f κ` is locally the weighted
  polynomial algebra in the `(n+1)κ` variables `x_{i,q}` of weights `q = 1..κ`
  (§2 of the paper: "the jet algebra is locally a weighted polynomial algebra");
* `YGG.sufficientlyDivisible`: every positive multiple `m` of `(n+1)κ·w_κ` (`w_κ = lcm(1..κ)`) is
  sufficiently divisible for `S` (§2.1 of the paper): the `m`-th Veronese subalgebra
  is generated in degree one, so `B_κ = O(m)` is a line bundle;
* `YGG.isIntegral`, `YGG.dimension_eq`: `Y_κ^GG` is integral of dimension `(n+1)κ`
  (Proposition 2.4 of the paper (i));
* `YGG.proj_isProper`, `YGG.isProperOver`, `YGG.fiber_isProperOver`: `π_κ` is proper (locally on `C`
  it is the projection `U × P(w) → U` with `P(w)` proper over `k`), hence `Y_κ^GG` is proper over `k`
  and the fibres `π_κ^{-1}(p)` are proper over `κ(p)` (base change);
* `YGG.isProjectiveOver`: `Y_κ^GG` is projective over `k` (`ykGG_integral_normal_projective`:
  `π_κ` is a projective morphism and so is `π_κ ≫ (C → Spec k)`).

All of these were proved inside `harmonic_intersection` (`HarmonicIntersection`) or are
hypotheses of `theta_shift_top_self_intersection_neg`; `negative_horizontal_curve`
(`PositiveLineCore`, Lemma 2.5 of the paper) needs them as public lemmas.

The proofs only unfold `MMSetup.cone`, `MMSetup.seed`, `jetAlgebra`, `YGG`, `YGG.proj` to the
`weightedJetProjectivization` of the twisted affine cone and apply `puncturedCone_spec`,
`jetGradedAlgebra_isLocallyWeightedPolynomial`, `veronese_generation_multiple`,
`ykGG_integral_normal_projective`, `relativeProj_locallyWeighted_localProduct` and
`local_weightedProjToSpec_isProper`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

section

variable {K : Type u} [Field K] {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f]

/-- The seed section `s : C → 𝒵` is a closed immersion (a section of a separated morphism). -/
theorem MMSetup.seed_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion (MMSetup.seed f).1 :=
  AlgebraicGeometry.IsClosedImmersion.of_section (MMSetup.cone f).hom (MMSetup.seed f).1
    (MMSetup.seed f).2

/-- The seed section lands in the punctured cone `Z^× ⊂ 𝒵`. -/
theorem MMSetup.seed_mem_punctured (c : C.toScheme) :
    (MMSetup.seed f).1.base c ∈ MMSetup.punctured f := by
  obtain ⟨s', hs'⟩ := seedSection_mem_punctured X.embedding (MMSetup.E (f := f)) f
    (MMSetup.coord (f := f)) (MMSetup.hcoord (f := f)) (MMSetup.E (f := f)).deg_pos
    (fun j => seedSection_equations_vanish X.embedding (MMSetup.E (f := f)) f
      (MMSetup.coord (f := f)) (MMSetup.hcoord (f := f)) j)
  have hmem : ((MMSetup.punctured f).ι.base (s' c)) ∈ MMSetup.punctured f := (s' c).property
  have heq : (s' ≫ (MMSetup.punctured f).ι) c = (MMSetup.seed f).1 c :=
    congrArg (fun g => g c) hs'
  rw [← heq]
  exact hmem

/-- `Z^× → C` is smooth of relative dimension `n + 1` (`n = dim X`). -/
theorem MMSetup.punctured_smoothOfRelativeDimension {n : ℕ} (hn : X.toVariety.dim = n) :
    AlgebraicGeometry.SmoothOfRelativeDimension (n + 1)
      ((MMSetup.punctured f).ι ≫ (MMSetup.cone f).hom) := by
  letI : AlgebraicGeometry.SmoothOfRelativeDimension n
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    smoothOfRelativeDimension_of_dim (X := X) hn
  exact (puncturedCone_spec (n := n) X.embedding (MMSetup.E (f := f)) f (MMSetup.coord (f := f))
    (MMSetup.hcoord (f := f))).2.1

/-- The jet algebra `S = jetAlgebra f κ` is locally the weighted polynomial algebra in the variables
`(i, q) ∈ Fin (n+1) × Fin κ` of weight `q + 1`. -/
theorem YGG.jetAlgebra_isLocallyWeightedPolynomial {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) :
    (jetAlgebra f κ).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin κ) => ((iq.down.2 : ℕ) + 1))
      (fun _ => Nat.succ_pos _) := by
  letI := MMSetup.seed_isClosedImmersion f
  letI := MMSetup.punctured_smoothOfRelativeDimension f hn
  exact jetGradedAlgebra_isLocallyWeightedPolynomial (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 (MMSetup.punctured f) (MMSetup.seed_mem_punctured f) n κ

/-- Every positive multiple `m` of `(n+1)κ·w_κ` is sufficiently divisible for the jet algebra
(Proposition 2.4 of the paper). -/
theorem YGG.sufficientlyDivisible {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) (hκ : 1 ≤ κ)
    (m : ℕ) (hm : 0 < m) (hdiv : (n + 1) * κ * jetWeight κ ∣ m) :
    (jetAlgebra f κ).SufficientlyDivisible m := by
  have hloc := YGG.jetAlgebra_isLocallyWeightedPolynomial f hn κ
  obtain ⟨mult, hmult⟩ := hdiv
  have hprod : 0 < ((n + 1) * κ * jetWeight κ) * mult := by
    rw [← hmult]
    exact hm
  have hmult_pos : 0 < mult := Nat.pos_of_mul_pos_left hprod
  let σ := ULift.{u} (Fin (n + 1) × Fin κ)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
  have hw : ∀ i, w i ∈ Finset.Icc 1 κ := by
    intro i
    simp [w]
  have hSuff0 := veronese_generation_multiple (jetAlgebra f κ) w hw hloc mult hmult_pos
  have hcard : Fintype.card σ = (n + 1) * κ := by
    simp [σ]
  have hEq : mult * (Fintype.card σ * jetWeight κ) = m := by
    rw [hcard]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmult.symm
  rw [← hEq]
  exact hSuff0

/-- Every weight `q ≤ κ` divides a multiple of `(n+1)κ·w_κ`. -/
theorem YGG.dvd_of_dvd_mul_jetWeight (n κ m : ℕ) (hdiv : (n + 1) * κ * jetWeight κ ∣ m) :
    ∀ q ∈ Finset.Icc 1 κ, q ∣ m := by
  intro q hq
  exact dvd_trans (dvd_mul_of_dvd_right (Finset.dvd_lcm hq) ((n + 1) * κ)) hdiv

/-- `π_κ : Y_κ^GG → C` is proper: locally on `C` it is `U × P(w) → U`. -/
theorem YGG.proj_isProper {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) :
    AlgebraicGeometry.IsProper (YGG.proj f κ) := by
  have hS := YGG.jetAlgebra_isLocallyWeightedPolynomial f hn κ
  let σ := ULift.{u} (Fin (n + 1) × Fin κ)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  have hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  let pC : C.toScheme ⟶ AlgebraicGeometry.Spec (CommRingCat.of K) :=
    C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)
  letI : AlgebraicGeometry.IsProper pC := C.isProper
  obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct.{u, u} pC (jetAlgebra f κ) w hw hS
  letI : AlgebraicGeometry.IsProper
      (weightedProjectiveSpace K w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    unfold weightedProjectiveSpace
    exact MiyaokaMori.WeightedJets.local_weightedProjToSpec_isProper
      (R := K) (ι := σ) (w := fun i => (⟨w i, hw i⟩ : ℕ+))
  change AlgebraicGeometry.IsProper (AlgebraicGeometry.Scheme.relativeProj (jetAlgebra f κ)).hom
  rw [AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover
    (P := @AlgebraicGeometry.IsProper) 𝒰]
  intro i
  obtain ⟨φ, hφ, _⟩ := h𝒰 i
  change AlgebraicGeometry.IsProper
    (CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.relativeProj (jetAlgebra f κ)).hom
      (𝒰.f i))
  rw [← hφ]
  infer_instance

/-- `Y_κ^GG` is proper over `k`. -/
theorem YGG.isProperOver {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) :
    IsProperOver K (YGG f κ) := by
  letI := YGG.proj_isProper f hn κ
  letI : AlgebraicGeometry.IsProper (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    C.isProper
  change AlgebraicGeometry.IsProper
    (YGG.proj f κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
  infer_instance

/-- The fibres of `π_κ` are proper over the residue fields. -/
theorem YGG.fiber_isProperOver {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) (p : C.toScheme) :
    letI := (YGG.proj f κ).fiberOverSpecResidueField p
    IsProperOver (C.toScheme.residueField p) ((YGG.proj f κ).fiber p) := by
  letI := YGG.proj_isProper f hn κ
  letI := (YGG.proj f κ).fiberOverSpecResidueField p
  change AlgebraicGeometry.IsProper
    (CategoryTheory.Limits.pullback.snd (YGG.proj f κ) (C.toScheme.fromSpecResidueField p))
  infer_instance

end

section

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f]

/-- `Y_κ^GG` is integral (`κ ≥ 1`). -/
theorem YGG.isIntegral {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) (hκ : 1 ≤ κ) :
    AlgebraicGeometry.IsIntegral (YGG f κ) :=
  (ykGG_integral_normal_projective (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 n κ hκ
    (YGG.jetAlgebra_isLocallyWeightedPolynomial f hn κ)).1

/-- `dim Y_κ^GG = (n + 1) κ` (`κ ≥ 1`). -/
theorem YGG.dimension_eq {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) (hκ : 1 ≤ κ) :
    (YGG f κ).dimension = (n + 1) * κ :=
  (ykGG_integral_normal_projective (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 n κ hκ
    (YGG.jetAlgebra_isLocallyWeightedPolynomial f hn κ)).2.2.2.2

/-- `Y_κ^GG → Spec k` is a projective morphism (`κ ≥ 1`). -/
theorem YGG.isProjectiveMorphism_over {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) (hκ : 1 ≤ κ) :
    AlgebraicGeometry.IsProjectiveMorphism
      (YGG f κ ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  (ykGG_integral_normal_projective (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 n κ hκ
    (YGG.jetAlgebra_isLocallyWeightedPolynomial f hn κ)).2.2.2.1

/-- `Y_κ^GG` is projective over `k` (`κ ≥ 1`). -/
theorem YGG.isProjectiveOver {n : ℕ} (hn : X.toVariety.dim = n) (κ : ℕ) (hκ : 1 ≤ κ) :
    IsProjectiveOver K (YGG f κ) :=
  (isProjectiveOver_iff_isProjectiveMorphism K (YGG f κ)).mpr
    (YGG.isProjectiveMorphism_over f hn κ hκ)

end

end
