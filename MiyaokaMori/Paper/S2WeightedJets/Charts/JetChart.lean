import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConePunctured
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetAlgebraLocallyWeightedPolynomial
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothRelativeDimensionOfDim

/-! # Jet charts and weighted coordinates

Jet charts and weighted coordinates on `Y_k^GG` (§2.2 of the paper: "locally over `C`, `Y_k^GG` is
a product with the weighted projective space"): the weights `jetWeights n κ` (the coordinate
`x_{i,q}` has weight `q`); a jet chart over an affine open `V ⊆ C`, obtained from the local
coordinates `J_k^s|_V ≅ 𝔸^{(n+1)κ}_V` (compatible with the rescaling of the jet parameter) as
`Y_k^GG|_V ≅ V × ℙ(w)`; the chart sends a `K`-point `x : Spec K → Y_k^GG` lying over `V` to its
`K`-point of `ℙ(w)` (`fiberCoords`, a morphism `Spec K → ℙ(w)`), compatibly with `x` over `k`
(`fiberCoords_over`).

The chart is `relativeProj_locallyWeighted_exists_affine_chart`: it takes the atlas chart
`U_i ∋ c` of the `IsLocallyWeightedPolynomial` hypothesis, applies
`relativeProj_locallyWeighted_chart` and transports along Mathlib's `pullbackRestrictIsoRestrict`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The weights of the jet coordinates `x_{i,q}` (`i ≤ n`, `1 ≤ q ≤ κ`): `x_{i,q}` has weight `q`;
the index `q` is recorded in `Fin κ` starting from `0`, so the weight is `q + 1`.
The index set is lifted to `Type u` with `ULift.{u}`, because `weightedProjectiveSpace` requires
`σ : Type u` (the universe of `k`). -/
def jetWeights (n κ : ℕ) : ULift.{u} (Fin (n + 1) × Fin κ) → ℕ := fun p => (p.down.2 : ℕ) + 1

theorem jetWeights_pos (n κ : ℕ) : ∀ p, 0 < jetWeights.{u} n κ p := by
  intro p
  simp [jetWeights]

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- A jet chart over an open `V ⊆ C`: jet coordinates `x_{i,q} ∈ S_q(V)` with
`S|_V = O_V[x_{i,q}]` (weighted polynomial algebra), so that
`Y_k^GG|_V ≅ V ×_k ℙ(jetWeights n κ)` compatibly with the projection to `V`.
(`fiberCoords` below gives the `K`-point of `ℙ(w)` of a `K`-point of `Y_k^GG` directly as a
morphism `Spec K ⟶ ℙ(w)`, not through classes of tuples.) -/
structure jetChart (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (V : C.toScheme.Opens) where
  coords : ∀ p : Fin (X.toVariety.dim + 1) × Fin κ,
    (((jetAlgebra f κ).part (jetWeights.{u} X.toVariety.dim κ ⟨p⟩)).val.obj (Opposite.op V) : Type u)
  iso : ((YGG.proj f κ) ⁻¹ᵁ V).toScheme ≅
    CategoryTheory.Limits.pullback (V.ι ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      (weightedProjectiveSpace k (jetWeights X.toVariety.dim κ) (jetWeights_pos _ _)
        ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  iso_fst : iso.hom ≫ CategoryTheory.Limits.pullback.fst _ _ = YGG.proj f κ ∣_ V

/-- **Affine jet-chart lemma, generic form** (§2.2 of the paper:
"locally over `C`, `Y_k^GG` is a product with the weighted projective space").

`S` is a graded quasi-coherent algebra on the `k`-scheme `X` that is locally a weighted polynomial
algebra with weights `w` (atlas form, `IsLocallyWeightedPolynomial`). Every point `c` has an affine
open neighbourhood `V` (a chart of the atlas) with `π⁻¹(V) ≅ V ×_k P_k(w)` compatibly with the
projection to `V`, where `π : Proj_X S → X`.

Proof: take the atlas chart `U_i ∋ c`; `relativeProj_locallyWeighted_chart` gives
`π ×_X U_i ≅ U_i ×_k P_k(w)` over `U_i` (squares (A) Stacks 01NQ, (B) the atlas isomorphism,
(C) Stacks 01N2 base change); Mathlib's `pullbackRestrictIsoRestrict` identifies `π ×_X U_i`
with the open subscheme `π⁻¹(U_i)`, and `pullbackRestrictIsoRestrict_hom_morphismRestrict` turns
`pullback.snd` into `π ∣_ U_i`. -/
theorem relativeProj_locallyWeighted_exists_affine_chart {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}}
    (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    {S : X.GradedQCAlgebra} {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) (c : X) :
    ∃ V : X.Opens, AlgebraicGeometry.IsAffineOpen V ∧ c ∈ V ∧
      ∃ e : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V).toScheme ≅
          CategoryTheory.Limits.pullback (V.ι ≫ pX)
            (weightedProjectiveSpace k w hw ↘
              AlgebraicGeometry.Spec (CommRingCat.of k)),
        e.hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
          (AlgebraicGeometry.Scheme.relativeProj S).hom ∣_ V := by
  obtain ⟨𝒜⟩ := hS
  obtain ⟨i, hi⟩ := 𝒜.covers c
  obtain ⟨φ, hφ, -⟩ := relativeProj_locallyWeighted_chart pX S w hw 𝒜 i
  refine ⟨(𝒜.chart i).toOpens, (𝒜.chart i).2, hi,
    (AlgebraicGeometry.pullbackRestrictIsoRestrict (AlgebraicGeometry.Scheme.relativeProj S).hom
      (𝒜.chart i).toOpens).symm ≪≫ φ, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hφ,
    ← AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict, Iso.inv_hom_id_assoc]

/-- The jet algebra is locally a weighted polynomial algebra with weights `jetWeights n κ`
(`jetGradedAlgebra_isLocallyWeightedPolynomial`);
the hypotheses (`MMSetup.cone`, `MMSetup.seed`, `MMSetup.punctured` and `puncturedCone_spec`) are
derived from `MMSetup`. -/
theorem jetAlgebra_isLocallyWeightedPolynomial (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) :
    (jetAlgebra f κ).IsLocallyWeightedPolynomial
      (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _) := by
  let _ : AlgebraicGeometry.SmoothOfRelativeDimension X.toVariety.dim
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    exact smoothOfRelativeDimension_of_dim (X := X) rfl
  let Z := MMSetup.cone f
  let s := (MMSetup.seed f).1
  let hs := (MMSetup.seed f).2
  let Zx := MMSetup.punctured f
  have hp := puncturedCone_spec (n := X.toVariety.dim) X.embedding
    (MMSetup.E : EmbeddingEquations k X.embedding (MMSetup.δ (f := f)))
    f MMSetup.coord (MMSetup.hcoord (f := f))
  have hsZx : ∀ c : C.toScheme, s.base c ∈ Zx := by
    obtain ⟨s', hs'⟩ := seedSection_mem_punctured X.embedding
      (MMSetup.E : EmbeddingEquations k X.embedding (MMSetup.δ (f := f))) f
      MMSetup.coord (MMSetup.hcoord (f := f)) (MMSetup.E).deg_pos
      (fun j => seedSection_equations_vanish X.embedding (MMSetup.E) f MMSetup.coord
        (MMSetup.hcoord (f := f)) j)
    intro c
    have hmem : (Zx.ι.base (s' c)) ∈ Zx := (s' c).property
    have heq : (s' ≫ Zx.ι) c = s c := by
      change (s' ≫ (puncturedCone (seedLineBundle X.embedding f) X.embDim (MMSetup.E).deg
        (MMSetup.E).deg_pos (MMSetup.E).F (MMSetup.E).homogeneous).ι) c =
        ((seedSection (seedLineBundle X.embedding f) X.embDim MMSetup.coord
          (MMSetup.E).deg (MMSetup.E).F (MMSetup.E).homogeneous
          (fun j => seedSection_equations_vanish X.embedding (MMSetup.E) f MMSetup.coord
            (MMSetup.hcoord (f := f)) j)).1) c
      exact congrArg (fun g => g c) hs'
    rw [← heq]
    exact hmem
  let _ : AlgebraicGeometry.IsClosedImmersion s :=
    AlgebraicGeometry.IsClosedImmersion.of_section Z.hom s hs
  let _ : AlgebraicGeometry.SmoothOfRelativeDimension (X.toVariety.dim + 1)
      (Zx.ι ≫ Z.hom) := by
    change AlgebraicGeometry.SmoothOfRelativeDimension (X.toVariety.dim + 1)
      ((puncturedCone (seedLineBundle X.embedding f) X.embDim (MMSetup.E).deg
        (MMSetup.E).deg_pos (MMSetup.E).F (MMSetup.E).homogeneous).ι ≫
        (twistedAffineCone (seedLineBundle X.embedding f) X.embDim (MMSetup.E).deg
          (MMSetup.E).F (MMSetup.E).homogeneous).hom)
    exact hp.2.1
  have hloc' := jetGradedAlgebra_isLocallyWeightedPolynomial Z s hs Zx hsZx
    X.toVariety.dim κ
  change ((jetGradedAlgebra (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) =>
        (iq.down.2 : ℕ) + 1)
      (fun _ => Nat.succ_pos _)
  exact hloc'

/-- Every point of `C` lies in the base open of some jet chart. -/
theorem jetChart.exists_mem (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (c : C.toScheme) :
    ∃ V : C.toScheme.Opens, AlgebraicGeometry.IsAffineOpen V ∧ c ∈ V ∧ Nonempty (jetChart f κ V) := by
  have hloc := jetAlgebra_isLocallyWeightedPolynomial f κ
  obtain ⟨V, hVaff, hmem, e, he⟩ := relativeProj_locallyWeighted_exists_affine_chart
    (pX := C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (S := jetAlgebra f κ) (w := jetWeights.{u} X.toVariety.dim κ)
    (hw := jetWeights_pos _ _) hloc c
  refine ⟨V, hVaff, hmem, ?_⟩
  let chart : jetChart f κ V :=
    { coords := fun _ => 0
      iso := e
      iso_fst := he }
  exact ⟨chart⟩

/-- The fiber coordinates of a chart: the weighted projective point, i.e. the morphism
`Spec K → ℙ(w)`, of a `K`-point `x : Spec K → Y_k^GG` lying over `V`. The point `x` factors through
the open immersion `π_k⁻¹(V) ↪ Y_k^GG` (`hx`); compose with the chart isomorphism and the second
projection. (This is not read as "a class of nonzero tuples modulo weighted scaling", which would
need a non-canonical tuple representative; tuple coordinates over `K` are produced downstream after
a finite extension, via `pointOfTuple`.) -/
noncomputable def jetChart.fiberCoords {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {V : C.toScheme.Opens} (chart : jetChart f κ V) {K : Type u} [Field K]
    (x : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ YGG f κ)
    (hx : Set.range (x ≫ YGG.proj f κ).base ⊆ V) :
    AlgebraicGeometry.Spec (CommRingCat.of K) ⟶
      weightedProjectiveSpace k (jetWeights X.toVariety.dim κ) (jetWeights_pos _ _) :=
  AlgebraicGeometry.IsOpenImmersion.lift ((YGG.proj f κ) ⁻¹ᵁ V).ι x
      (by
        rw [AlgebraicGeometry.Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hx ⟨y, rfl⟩) ≫
    chart.iso.hom ≫ CategoryTheory.Limits.pullback.snd _ _

/-- `fiberCoords` is a morphism over `k`: its structure morphism to `Spec k` is that of `x` (the
pullback square, `iso_fst` and the definition of `YGG.over`). Hence, when `K` carries the
`k`-algebra structure induced by `x`, `fiberCoords` is a `weightedProjectiveSpace.KPoint`. -/
theorem jetChart.fiberCoords_over {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {V : C.toScheme.Opens} (chart : jetChart f κ V) {K : Type u} [Field K]
    (x : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ YGG f κ)
    (hx : Set.range (x ≫ YGG.proj f κ).base ⊆ V) :
    chart.fiberCoords x hx ≫
        (weightedProjectiveSpace k (jetWeights X.toVariety.dim κ) (jetWeights_pos _ _)
          ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = x ≫ (YGG f κ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  unfold jetChart.fiberCoords
  simp only [CategoryTheory.Category.assoc]
  rw [← CategoryTheory.Limits.pullback.condition, reassoc_of% chart.iso_fst,
    AlgebraicGeometry.morphismRestrict_ι_assoc, AlgebraicGeometry.IsOpenImmersion.lift_fac_assoc]
  rfl

end
