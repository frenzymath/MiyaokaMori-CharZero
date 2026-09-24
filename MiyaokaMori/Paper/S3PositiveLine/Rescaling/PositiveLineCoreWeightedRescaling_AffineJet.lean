import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCoreWeightedRescaling
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.AffineJetChartCoords
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetSchemeWeightPieceSectionsRingHom

/-! # The affine lift after finite base change: the affine-jet lemmas
(Lemma 3.1 of the paper; paper-faithful replacement of the two lemmas of
`PositiveLineCoreWeightedRescaling`)

`weighted_rescaling` (`PositiveLineCore`) is assembled from the two theorems of this file and
`exists_tau` :

* `weighted_rescaling_generic_affineJet` (the paper's
  paragraph "A generic affine representative", Lemma 3.1 of the paper): a **finite family of affine
  honest jet charts** `(V α, chart α)` covering `C` (all containing `η_C`), a finite cover
  `ρ = η ≫ ν₀ ≫ π_κ : C̃ → C`, and **one affine jet** `ĵ : Spec κ(η_{C̃}) → J_κ^s` over `η_{C̃} ≫ ρ`
  whose coordinate tuples `b α` in **every** chart (`affineJetCoord`) have `(q+1)`-th roots — the
  paper's "after a further finite extension, taken simultaneously for the finitely many charts"
  (Lemma 3.1 of the paper) — and whose coordinates in a designated chart `α₀` give the fiber
  coordinate of `η ≫ ν₀` at the generic point (`weightedPointOfCoords`);
* `weighted_rescaling_jet_of_affineJet` (in the companion
  module `BasedJetOfAffineJet`; the paragraph
  "The parameter line and the based jet", Lemma 3.1 of the paper): from these data, the line bundle
  `L`, the based jet `J` with nowhere-zero normalized tuple, and the identification of the fiber
  coordinate of its generic weighted point in the chart `α₀` with `weightedPointOfCoords (b α₀)`.
  Assembled from `exists_basedJet_of_affineJet` (`BasedJetOfChartFamily`),
  `HonestJetChart.fiberCoords_genericWeightedPoint` and `weightedPointOfCoords_scale`.

**Why the hypotheses are shaped this way.** A version working with the coordinate tuple of a **single**
chart `V ∋ η_C` would be **false**: a single-chart root hypothesis does not make the weighted orders at
points `y` with `ρ(y) ∉ V` integral, so no `L` exists in general (for `X = P¹`, `κ = 2`, `ρ = id`,
`A = O(1)`, charts `{x₀ ≠ 0}`, `{x₁ ≠ 0}` and the tuple `b = (0; 1, 0)`, the weighted order at `∞` in the
other chart is `-1/2`). This file therefore uses the paper's hypotheses (the tuples are the coordinates
of one affine jet `ĵ` in a finite chart family covering `C`, with roots in every chart). The paper's
argument (Lemma 3.1) is followed literally: the affine representative is one point
of `J_k^s ×_C Spec K`, `b_α` are its coordinates in each chart, and the roots are taken simultaneously.

Also here: `affineJetCoordAt` (the coordinate of an `R`-point of `J_κ^s` for any ring `R`, of which
`affineJetCoord` is the `K(C̃)` reading) with its naturality in the ring; the finite honest chart
cover `HonestJetChart.exists_finite_cover`; and the step "the fiber coordinate of `η ≫ ν₀` is the
weighted point of the transported affine lift", factored out as
`fiberCoords_generic_eq_weightedPointOfCoords_of_normalization`.

Two lemmas carry the genuinely new work: `HonestJetChart.exists_affineJet_of_tuple` (an `R`-point of `J_κ^s` over
`V` with prescribed coordinates in an honest chart) and
`HonestJetChart.exists_affineJetCoordAt_ne_zero_of_exists_ne_zero` (the coordinates of an affine jet
are not all zero in one honest chart iff not all zero in another; the paper's "the transitions have
no constant term", §2.1–2.2 of the paper).
The second is proved through `affineJetSectionsHom` (the coordinates of `ĵ` as a ring homomorphism
`S(W) →+* R` on the sections ring, compatible with the structure map and with restriction) and
`HonestJetChart.affineJetSectionsHom_ofPiece_eq_zero_of_forall_coords_eq_zero` (in an honest chart
whose coordinates all vanish on `ĵ`, every piece of positive weight vanishes on `ĵ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-! ## Coordinates of an `R`-point of the affine jet scheme -/

/-- The value in `R` of a chart coordinate `x ∈ S_m(V)` on an `R`-point `ĵ : Spec R → J_κ^s` of the
affine jet scheme lying over `V`: `x` is put into `Γ(J_κ^s, π⁻¹V)` by `BasedJet.partι`, pulled back
along `ĵ` to `Γ(Spec R, ⊤)` and read in `R` through `ΓSpecIso`. `affineJetCoord`
(`BasedJetOfChartFamily`) is this for `R = κ(η_{C̃})`, read in `K(C̃)`
(`affineJetCoord_eq_affineJetCoordAt`). -/
def affineJetCoordAt {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ} {R : CommRingCat.{u}}
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece V m) : R :=
  (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom
    ((ĵ.appLE _ ⊤ hV).hom
      (show Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
          (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V) from
        ((BasedJet.partι f κ m).val.app (Opposite.op V)).hom x))

/-- `affineJetCoord` is `affineJetCoordAt` read in `K(C̃)` through `functionFieldIsoResidueField`. -/
theorem affineJetCoord_eq_affineJetCoordAt {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece V m) :
    affineJetCoord ρ ĵ hV m x =
      (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
       ρ.source.toScheme.functionFieldIsoResidueField.inv.hom (affineJetCoordAt ĵ hV m x)) := rfl

/-- If `ĵ` lies over `V` then so does `g ≫ ĵ` (pointwise). -/
theorem top_le_preimage_comp_of_top_le {T T' Y : AlgebraicGeometry.Scheme.{u}} (g : T' ⟶ T)
    (ĵ : T ⟶ Y) {W : Y.Opens} (hV : (⊤ : T.Opens) ≤ ĵ ⁻¹ᵁ W) :
    (⊤ : T'.Opens) ≤ (g ≫ ĵ) ⁻¹ᵁ W :=
  fun s _ => @hV (g.base s) trivial

/-- **Naturality of the affine jet coordinates in the ring**: precomposing the `R`-point `ĵ` with
`Spec φ : Spec R' → Spec R` applies `φ` to its coordinates (`Scheme.appLE_comp_appLE`,
`Scheme.ΓSpecIso_naturality`). -/
theorem affineJetCoordAt_SpecMap_comp {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (hV' : (⊤ : (AlgebraicGeometry.Spec R').Opens) ≤
      (AlgebraicGeometry.Spec.map φ ≫ ĵ) ⁻¹ᵁ
        ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece V m) :
    affineJetCoordAt (AlgebraicGeometry.Spec.map φ ≫ ĵ) hV' m x =
      φ.hom (affineJetCoordAt ĵ hV m x) := by
  unfold affineJetCoordAt
  have h1 : (AlgebraicGeometry.Spec.map φ ≫ ĵ).appLE _ ⊤ hV' =
      ĵ.appLE _ ⊤ hV ≫ (AlgebraicGeometry.Spec.map φ).appLE ⊤ ⊤ (fun _ _ => trivial) :=
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : (AlgebraicGeometry.Spec.map φ).appLE ⊤ ⊤ (fun _ _ => trivial) =
      (AlgebraicGeometry.Spec.map φ).appTop := by
    rw [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    rfl
  have h3 := AlgebraicGeometry.Scheme.ΓSpecIso_naturality φ
  rw [h1, h2]
  change ((ĵ.appLE _ ⊤ hV ≫ (AlgebraicGeometry.Spec.map φ).appTop) ≫
    (AlgebraicGeometry.Scheme.ΓSpecIso R').hom).hom _ =
    ((ĵ.appLE _ ⊤ hV ≫ (AlgebraicGeometry.Scheme.ΓSpecIso R).hom) ≫ φ).hom _
  rw [Category.assoc, h3, Category.assoc]

/-! ## The finite honest chart family -/

/-- **A finite family of affine honest jet charts covering `C`, all containing `η_C`**
(Lemma 3.1 of the paper: "Fix finitely many jet charts `U_α` covering `C`"). From
`HonestJetChart.exists_mem`  at every point, a finite subcover
(`C` is quasi-compact, `Variety.compactSpace`); a nonempty open of the irreducible `C` contains the
generic point (`genericPoint_specializes`). The index type is the chosen finite set of points. -/
theorem HonestJetChart.exists_finite_cover (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → C.toScheme.Opens)
      (_ : ∀ α, AlgebraicGeometry.IsAffineOpen (V α)) (_ : ∀ α, HonestJetChart f κ (V α)),
      (∀ α, genericPoint C.toScheme ∈ V α) ∧ ∀ c : C.toScheme, ∃ α, c ∈ V α := by
  classical
  have hint : AlgebraicGeometry.IsIntegral C.toScheme := C.isIntegral
  choose V hV hmem hchart using HonestJetChart.exists_mem f κ
  have : CompactSpace C.toScheme := Variety.compactSpace C.toVariety
  obtain ⟨T, hT⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
    (fun c : C.toScheme => (V c : Set C.toScheme)) (fun c => (V c).isOpen)
    (fun c _ => Set.mem_iUnion.mpr ⟨c, hmem c⟩)
  refine ⟨T, inferInstance, fun t => V t, fun t => hV t, fun t => Classical.choice (hchart t),
    fun t => ?_, fun c => ?_⟩
  · exact (genericPoint_specializes (t : C.toScheme)).mem_open (V t).isOpen (hmem t)
  · obtain ⟨t, ht, hc⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ c))
    exact ⟨⟨t, ht⟩, hc⟩

/-! ## The two new lemmas -/

/-- **An affine jet with prescribed coordinates in an honest chart** (Lemma 3.1 of the paper:
"Choosing homogeneous coordinates for this preimage gives a nonzero affine representative
`(u_{i,q}^q)_{i,q}` of the weighted-projective point in `J_k^s ×_C Spec K`"). Let `(V, chart)` be an
honest jet chart, `K` a field, `y : Spec K → C` with image in `V`, and `v` a tuple in `K` indexed by
the chart coordinates. Then there is a `K`-point `ĵ : Spec K → J_κ^s` over `y` whose coordinates in
the chart are the `v i q`.

Natural-language proof. Write `U := (V, hV)` (affine), `S := jetAlgebra f κ`. The affine jet scheme
over `U` is `Spec` of the based jet algebra `J_κ(B_U, s^♯)` (`relativeJetScheme.chartRing U`; the
chart `Spec (chartRing U) → J_κ^s` is an open immersion with image `π⁻¹V`,
`relativeJetScheme.chart_isOpenImmersion`, `projChart_isPullback`-type identification of the image),
and `Γ(J_κ^s, π⁻¹V) ≅ chartRing U ≅ S(V)` (`relativeJetScheme.chartEquiv`,
`jetGradedAlgebra_sections_equiv_jetGradedAffineAlgebra`, `JetGradedAlgebraSectionsBridge`),
compatibly with `Γ(V) → S(V)` (`chartEquiv_unitHom`) and carrying `partι x` (for `x ∈ S_m(V)`) to
`ofPiece x` (`weightPartιApp`, same file). Honesty of the chart
(`chart.honest`: `ε : S(V) ≃+* Γ(V)[x_p]`, `ε (unitHom r) = C r`, `ε (ofPiece (coords p)) = X p`)
gives the `Γ(V)`-algebra map `ψ := eval₂Hom (y^♯ : Γ(V) → K) v ∘ ε : S(V) → K`, `x_p ↦ v p`,
restricting to `y^♯ : Γ(V) → Γ(Spec K) = K` on `Γ(V)`. By the affineness of `π⁻¹V ≅ Spec S(V)` over
`V`, `ψ` is a morphism `ĵ : Spec K → π⁻¹V ⊆ J_κ^s` with `ĵ ≫ π = y` (`Spec`–`Γ` adjunction on the
affine `π⁻¹V`), and `affineJetCoordAt ĵ _ (coords p) = ΓSpecIso (ĵ^♯ (partι (coords p))) =
ψ (ofPiece (coords p)) = eval₂Hom y^♯ v (X p) = v p`. ∎

The formal proof follows these lines with the helpers of
`JetSchemeWeightPieceSectionsRingHom`: `Θ := weightPartιRingHom` (bijective on the affine `V`,
`relativeJetScheme.weightPartιRingHom_bijective`) is the identification `S(V) ≅ Γ(J_κ^s, π⁻¹V)`,
`ĵ := Spec.map ψ ≫ hU.fromSpec` for the affine open `π⁻¹V` (`IsAffineOpen.appLE_SpecMap_fromSpec`,
`IsAffineOpen.eq_SpecMap_appLE_fromSpec`). Edge cases: `κ = 0` — `Fin 0` empty, `v` is the empty
tuple, `J_0^s = C` and `ĵ = y` works; `v = 0` allowed (the zero jet); `n = 0` fine. -/
theorem HonestJetChart.exists_affineJet_of_tuple {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {V : C.toScheme.Opens} (chart : HonestJetChart f κ V) {K : Type u} [Field K]
    (y : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ C.toScheme) (hy : Set.range y.base ⊆ V)
    (v : Fin (X.toVariety.dim + 1) → Fin κ → K) :
    ∃ (ĵ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶
        (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
      (_ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        = y)
      (hĵV : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of K)).Opens) ≤
        ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
          ⁻¹ᵁ V)),
      ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
        affineJetCoordAt ĵ hĵV _ (chart.coords (i, q)) = v i q := by
  classical
  let α := jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  let J := relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  have hVaff : AlgebraicGeometry.IsAffineOpen V := chart.isAffineOpen
  have hU : AlgebraicGeometry.IsAffineOpen (J.hom ⁻¹ᵁ V) :=
    AlgebraicGeometry.IsAffineHom.isAffine_preimage V hVaff
  have e : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of K)).Opens) ≤ y ⁻¹ᵁ V :=
    fun s _ => hy ⟨s, rfl⟩
  -- `y^♯ : Γ(C, V) → K`
  let ysh : Γ(C.toScheme, V) →+* K :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (y.appLE V ⊤ e).hom
  -- honesty of the chart
  obtain ⟨ε, φ, hφ, -, hunit, hcoords, -, -⟩ := chart.honest
  -- `ψ₀ : S(V) → K`, `x_p ↦ v p`, `r ↦ y^♯ r`
  let ψ₀ : (jetAlgebra f κ).sectionsRing V →+* K :=
    (MvPolynomial.eval₂Hom ysh (fun p : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) =>
      v p.down.1 p.down.2)).comp ε.toRingHom
  -- `Θ : S(V) ≃+* Γ(J, π⁻¹V)`
  obtain ⟨Θe, hΘe⟩ : ∃ Θe : (jetAlgebra f κ).sectionsRing V ≃+* Γ(J.left, J.hom ⁻¹ᵁ V),
      ∀ x, Θe x = GroupSchemeAction.weightPartιRingHom α V x :=
    ⟨RingEquiv.ofBijective _ (relativeJetScheme.weightPartιRingHom_bijective (k := k) (MMSetup.cone f)
      (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVaff⟩), fun _ => rfl⟩
  let ψ : Γ(J.left, J.hom ⁻¹ᵁ V) →+* K := ψ₀.comp Θe.symm.toRingHom
  have hψ : ∀ x : (jetAlgebra f κ).sectionsRing V,
      ψ (GroupSchemeAction.weightPartιRingHom α V x) = ψ₀ x := by
    intro x
    show ψ₀ (Θe.symm (GroupSchemeAction.weightPartιRingHom α V x)) = ψ₀ x
    rw [← hΘe, Θe.symm_apply_apply]
  let ĵ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ J.left :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec
  have hĵV := hU.top_le_preimage_SpecMap_fromSpec (CommRingCat.ofHom ψ)
  refine ⟨ĵ, ?_, hĵV, ?_⟩
  · -- `ĵ ≫ π = y`
    have h1 : hU.fromSpec ≫ J.hom =
        AlgebraicGeometry.Spec.map (J.hom.appLE V (J.hom ⁻¹ᵁ V) le_rfl) ≫ hVaff.fromSpec :=
      (hVaff.SpecMap_appLE_fromSpec J.hom hU le_rfl).symm
    have h2 := hVaff.eq_SpecMap_appLE_fromSpec y e
    have hcomp : J.hom.appLE V (J.hom ⁻¹ᵁ V) le_rfl ≫ CommRingCat.ofHom ψ =
        y.appLE V ⊤ e ≫ (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
      apply CommRingCat.hom_ext
      ext r
      show ψ ((J.hom.appLE V (J.hom ⁻¹ᵁ V) le_rfl).hom r) = ysh r
      rw [← AlgebraicGeometry.Scheme.Hom.app_eq_appLE,
        ← GroupSchemeAction.weightPartιRingHom_sectionsUnitHom α V r]
      refine (hψ ((jetAlgebra f κ).sectionsUnitHom V r)).trans ?_
      show MvPolynomial.eval₂Hom ysh _ (ε ((jetAlgebra f κ).sectionsUnitHom V r)) = ysh r
      rw [hunit r, MvPolynomial.eval₂Hom_C]
    refine Eq.trans ?_ h2.symm
    show (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ≫ J.hom = _
    rw [Category.assoc, h1, ← Category.assoc, ← AlgebraicGeometry.Spec.map_comp, hcomp]
  · -- the coordinates
    intro i q
    unfold affineJetCoordAt
    rw [hU.appLE_SpecMap_fromSpec (CommRingCat.ofHom ψ) hĵV]
    show (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        (ψ (GroupSchemeAction.weightPartιApp α _ V (chart.coords (i, q))))) = v i q
    refine (CommRingCat.hom_inv_apply (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)) _).trans ?_
    rw [← GroupSchemeAction.weightPartιRingHom_ofPiece α V _ (chart.coords (i, q))]
    refine (hψ ((jetAlgebra f κ).ofPiece V _ (chart.coords (i, q)))).trans ?_
    show MvPolynomial.eval₂Hom ysh _ (ε ((jetAlgebra f κ).ofPiece V _ (chart.coords (i, q)))) = v i q
    rw [hcoords (i, q), MvPolynomial.eval₂Hom_X']

/-! ### The sections-ring reading of `affineJetCoordAt` -/

/-- **The coordinates of an `R`-point as a ring homomorphism on the sections ring**:
`Ψ_W : S(W) →+* R`, `x ↦ ΓSpecIso (ĵ^♯ (Θ_W x))`, for `ĵ : Spec R → J_κ^s` over `W`, where
`Θ_W = weightPartιRingHom` puts `S(W) = ⊕_m S_m(W)` into `Γ(J_κ^s, π⁻¹W)`
(`JetSchemeWeightPieceSectionsRingHom`). `affineJetCoordAt` is `Ψ_W` on the pieces
(`affineJetCoordAt_eq_affineJetSectionsHom`); `Ψ_W` is compatible with the structure map
(`affineJetSectionsHom_sectionsUnitHom`) and with restriction
(`affineJetSectionsHom_sectionsRestrictHom`). -/
def affineJetSectionsHom {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ} {R : CommRingCat.{u}}
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {W : C.toScheme.Opens}
    (hW : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ W)) :
    (jetAlgebra f κ).sectionsRing W →+* R :=
  ((AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom.comp (ĵ.appLE _ ⊤ hW).hom).comp
    (GroupSchemeAction.weightPartιRingHom
      (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) W)

/-- `affineJetCoordAt` is `affineJetSectionsHom` on the pieces (`weightPartιRingHom_ofPiece`). -/
theorem affineJetCoordAt_eq_affineJetSectionsHom {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {R : CommRingCat.{u}}
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {W : C.toScheme.Opens}
    (hW : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ W))
    (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece W m) :
    affineJetCoordAt ĵ hW m x = affineJetSectionsHom ĵ hW ((jetAlgebra f κ).ofPiece W m x) := by
  have h := GroupSchemeAction.weightPartιRingHom_ofPiece
    (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) W m x
  exact congrArg (fun y => (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom ((ĵ.appLE _ ⊤ hW).hom y))
    h.symm

/-- `Ψ_W` on the structure map is `ĵ^♯ ∘ π^♯` (`weightPartιRingHom_sectionsUnitHom`). -/
theorem affineJetSectionsHom_sectionsUnitHom {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {R : CommRingCat.{u}}
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {W : C.toScheme.Opens}
    (hW : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ W))
    (r : Γ(C.toScheme, W)) :
    affineJetSectionsHom ĵ hW ((jetAlgebra f κ).sectionsUnitHom W r) =
      (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom ((ĵ.appLE _ ⊤ hW).hom
        (((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.app
          W).hom r)) := by
  exact congrArg (fun y => (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom ((ĵ.appLE _ ⊤ hW).hom y))
    (GroupSchemeAction.weightPartιRingHom_sectionsUnitHom
      (jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ) W r)

/-- `Ψ` is compatible with restriction: `Ψ_W (x|_W) = Ψ_{W'} x` for `W ≤ W'`
(`weightPartιRingHom_restrict` and `Scheme.Hom.map_appLE`). -/
theorem affineJetSectionsHom_sectionsRestrictHom {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {R : CommRingCat.{u}}
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {W W' : C.toScheme.Opens} (h : W ≤ W')
    (hW : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ W))
    (hW' : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ W'))
    (x : (jetAlgebra f κ).sectionsRing W') :
    affineJetSectionsHom ĵ hW ((jetAlgebra f κ).sectionsRestrictHom h x) =
      affineJetSectionsHom ĵ hW' x := by
  let α := jetRescalingAction (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  let J := relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  have h' : J.hom ⁻¹ᵁ W ≤ J.hom ⁻¹ᵁ W' := fun s hs => h hs
  have hr := GroupSchemeAction.weightPartιRingHom_restrict α h h' x
  have key := AlgebraicGeometry.Scheme.Hom.map_appLE ĵ hW (homOfLE h').op
  refine (congrArg (fun y => (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom
    ((ĵ.appLE _ ⊤ hW).hom y)) hr.symm).trans ?_
  exact congrArg (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key)
      (GroupSchemeAction.weightPartιRingHom α W' x))

/-- **If all coordinates of `ĵ` in an honest chart vanish, `Ψ` kills every piece of positive
weight** (§2.1–2.2 of the paper: the coordinates generate the positive part without constant
terms). Honesty gives `ε : S(V) ≃+* Γ(V)[x_p]` with `ε (unit r) = C r`, `ε (coords p) = X p`, and
`S_m(V)` = the weighted-homogeneous polynomials of weight `m`; so `Ψ ∘ ε⁻¹` is the evaluation
`eval₂Hom (Ψ ∘ unit) (Ψ (coords ·)) = eval₂Hom (Ψ ∘ unit) 0` (`MvPolynomial.ringHom_ext`), which
reads the constant coefficient (`eval₂Hom_zero'_apply`), and a weighted-homogeneous polynomial of
weight `m ≠ 0` has constant coefficient `0` (`IsWeightedHomogeneous.coeff_eq_zero`). -/
theorem HonestJetChart.affineJetSectionsHom_ofPiece_eq_zero_of_forall_coords_eq_zero
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ} {R : CommRingCat.{u}}
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens} (chart : HonestJetChart f κ V)
    (hV : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (h0 : ∀ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      affineJetCoordAt ĵ hV _ (chart.coords (i, q)) = 0)
    {m : ℕ} (hm : m ≠ 0) (x : (jetAlgebra f κ).sectionsPiece V m) :
    affineJetSectionsHom ĵ hV ((jetAlgebra f κ).ofPiece V m x) = 0 := by
  obtain ⟨ε, -, -, hgrade, hunit, hcoords, -, -⟩ := chart.honest
  set Ψ := affineJetSectionsHom ĵ hV with hΨ
  have key : Ψ.comp ε.symm.toRingHom =
      MvPolynomial.eval₂Hom (Ψ.comp ((jetAlgebra f κ).sectionsUnitHom V))
        (fun _ : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) => (0 : R)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      show Ψ (ε.symm (MvPolynomial.C r)) = Ψ ((jetAlgebra f κ).sectionsUnitHom V r)
      rw [← hunit r, ε.symm_apply_apply]
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      show Ψ (ε.symm (MvPolynomial.X ⟨p.down⟩)) = 0
      rw [← hcoords p.down, ε.symm_apply_apply, hΨ, ← affineJetCoordAt_eq_affineJetSectionsHom]
      exact h0 p.down.1 p.down.2
  have hx : (ε ((jetAlgebra f κ).ofPiece V m x)).IsWeightedHomogeneous
      (jetWeights.{u} X.toVariety.dim κ) m :=
    (hgrade m _).mp ⟨x, rfl⟩
  calc Ψ ((jetAlgebra f κ).ofPiece V m x)
      = (Ψ.comp ε.symm.toRingHom) (ε ((jetAlgebra f κ).ofPiece V m x)) := by
        show Ψ _ = Ψ (ε.symm (ε _))
        rw [ε.symm_apply_apply]
    _ = (Ψ.comp ((jetAlgebra f κ).sectionsUnitHom V))
          (MvPolynomial.constantCoeff (ε ((jetAlgebra f κ).ofPiece V m x))) := by
        rw [key]
        exact MvPolynomial.eval₂Hom_zero'_apply _ _
    _ = 0 := by
        rw [MvPolynomial.constantCoeff_eq, hx.coeff_eq_zero 0 (by rw [map_zero]; exact hm.symm)]
        exact map_zero _

/-- **Non-vanishing of the coordinates of an affine jet is chart-independent**
(§2.1–2.2 of the paper, (2.7): the transition between two jet charts is a weighted
homogeneous substitution with **no constant term** and an inverse of the same form, so a jet whose
coordinates vanish in one chart has vanishing coordinates in every chart). Let `ĵ : Spec K → J_κ^s`
lie over `V ∩ V'` for honest charts `(V, chart)`, `(V', chart')`. If some coordinate of `ĵ` in the
first chart is nonzero, then some coordinate in the second chart is nonzero.

Natural-language proof (contrapositive: all `chart'`-coordinates vanish ⇒ all `chart`-coordinates
vanish). Write `c := π(ĵ) ∈ V ∩ V'` for the image of the point of `Spec K`, `S := jetAlgebra f κ`.
1. `exists_basicOpen_le_affine_inter` (Mathlib; `C` is separated so `V ∩ V'` is covered by common
   basic opens) gives `g ∈ Γ(V)`, `g' ∈ Γ(V')` with `D := V.basicOpen g = V'.basicOpen g' ∋ c`.
2. For `x ∈ S_m(W)` (`W ∈ {V, V', D}`, `c ∈ W`) put `ĵ^♯ x := ΓSpecIso (ĵ.appLE (π⁻¹W) ⊤ _ (partι x)) ∈ K`.
   Restriction compatibility: `ĵ^♯ (x|_D) = ĵ^♯ x` (`partι` is a morphism of sheaves; `appLE` is
   compatible with restriction, `Scheme.Hom.appLE_map`). Multiplicativity: `ĵ^♯ (x·x') = ĵ^♯ x · ĵ^♯ x'`
   and `ĵ^♯ (r·x) = y^♯ r · ĵ^♯ x` for `r ∈ Γ(W)` (`partι` of the weight pieces is compatible with the
   products of the graded algebra, `weightPartιApp_sectionsGMul`, `JetGradedAlgebraSectionsBridge`).
3. Honesty of `chart'`: every `x' ∈ S_m(V')`, `m ≥ 1`, is a `Γ(V')`-polynomial in the `coords'` with no
   constant term (`ε' x'` is weighted homogeneous of weight `m ≥ 1`, hence in the ideal `(X_p)`). So if
   all `ĵ^♯ (coords' p) = 0` then `ĵ^♯ x' = 0` for every `x' ∈ S_m(V')`, `m ≥ 1` (step 2).
4. Quasi-coherence of `S` (`GradedQCAlgebra`): `S_m(D) = S_m(V')[1/g']`, i.e. every `z ∈ S_m(D)` is
   `x'|_D / g'^N` for some `x' ∈ S_m(V')`, `N`. Hence `ĵ^♯ z · (y^♯ g')^N = ĵ^♯ (x'|_D) = ĵ^♯ x' = 0`
   and `y^♯ g' ≠ 0` (`c ∈ D(g')`, `K` a field), so `ĵ^♯ z = 0` for all `z ∈ S_m(D)`, `m ≥ 1`.
5. In particular `ĵ^♯ (coords p) = ĵ^♯ ((coords p)|_D) = 0` for every `p` (`coords p ∈ S_{q+1}(V)`,
   `q + 1 ≥ 1`), contradicting the hypothesis. ∎

The formal proof follows these lines. The three pieces: (i) `ĵ^♯` on the pieces
is the ring homomorphism `affineJetSectionsHom` (`Ψ_W := ΓSpecIso ∘ ĵ^♯ ∘ Θ_W` on
`S(W) = ⊕_m S_m(W)`; `affineJetCoordAt_eq_affineJetSectionsHom`), compatible with the structure map
(`affineJetSectionsHom_sectionsUnitHom`) and with restriction
(`affineJetSectionsHom_sectionsRestrictHom`, from `weightPartιRingHom_restrict` and
`Scheme.Hom.map_appLE`); (ii) step 3 is
`HonestJetChart.affineJetSectionsHom_ofPiece_eq_zero_of_forall_coords_eq_zero`
(`MvPolynomial.ringHom_ext`, `eval₂Hom_zero'_apply`, `IsWeightedHomogeneous.coeff_eq_zero`);
(iii) step 4 is the quasi-coherence of the piece `S_m` on the affine `V'`
(`Scheme.Modules.exists_pow_smul_eq_map_basicOpen`: `g'^N • z = x'|_D`), the scalar action being
multiplication by the structure map (`sectionsUnitHom_mul_ofPiece`) and `y^♯ g' ≠ 0` from
`RingedSpace.isUnit_res_basicOpen`. The point `c` is the unique point of `Spec K`
(`Unique (PrimeSpectrum K)`). Edge cases: `κ = 0` — `Fin 0` empty, `hne` impossible, vacuous;
`V = V'` — trivial; `K` any field (not necessarily over `k`). -/
theorem HonestJetChart.exists_affineJetCoordAt_ne_zero_of_exists_ne_zero
    {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ} {K : Type u} [Field K]
    (ĵ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V V' : C.toScheme.Opens} (chart : HonestJetChart f κ V) (chart' : HonestJetChart f κ V')
    (hV : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of K)).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (hV' : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of K)).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V'))
    (hne : ∃ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      affineJetCoordAt ĵ hV _ (chart.coords (i, q)) ≠ 0) :
    ∃ (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
      affineJetCoordAt ĵ hV' _ (chart'.coords (i, q)) ≠ 0 := by
  classical
  let J := relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
  by_contra hcon
  push Not at hcon
  obtain ⟨i, q, hiq⟩ := hne
  apply hiq
  -- the (unique) point of `Spec K` and its image `c ∈ V ⊓ V'`
  let pt : (AlgebraicGeometry.Spec (CommRingCat.of K)) := (default : PrimeSpectrum K)
  have hpt : ∀ s : (AlgebraicGeometry.Spec (CommRingCat.of K)), s = pt := fun s =>
    Subsingleton.elim (α := PrimeSpectrum K) s pt
  have hc : J.hom.base (ĵ.base pt) ∈ V ⊓ V' := ⟨@hV pt trivial, @hV' pt trivial⟩
  -- a common basic open `D = D_V(g) = D_{V'}(g') ∋ c`
  obtain ⟨g, g', hgg', hcg⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter chart.isAffineOpen chart'.isAffineOpen _ hc
  rw [hgg'] at hcg
  have hDV' : C.toScheme.basicOpen g' ≤ V' := C.toScheme.basicOpen_le g'
  have hDV : C.toScheme.basicOpen g' ≤ V := by
    rw [← hgg']
    exact C.toScheme.basicOpen_le g
  have hD : (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of K)).Opens) ≤
      ĵ ⁻¹ᵁ (J.hom ⁻¹ᵁ C.toScheme.basicOpen g') := by
    intro s _
    rw [hpt s]
    exact hcg
  -- `Ψ_D (g'|_D) ≠ 0`: `g'|_D` is a unit
  have hg'unit : affineJetSectionsHom ĵ hD ((jetAlgebra f κ).sectionsUnitHom _
      ((C.toScheme.presheaf.map (homOfLE hDV').op).hom g')) ≠ 0 := by
    rw [affineJetSectionsHom_sectionsUnitHom]
    exact (((C.toScheme.toRingedSpace.isUnit_res_basicOpen g').map
      (J.hom.app (C.toScheme.basicOpen g')).hom).map (ĵ.appLE _ ⊤ hD).hom).map
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom |>.ne_zero
  -- `Ψ_D` kills every piece of positive weight on `D` (quasi-coherence: `S_m(D) = S_m(V')[1/g']`)
  have hkill : ∀ (m : ℕ), m ≠ 0 → ∀ s : (jetAlgebra f κ).sectionsPiece (C.toScheme.basicOpen g') m,
      affineJetSectionsHom ĵ hD ((jetAlgebra f κ).ofPiece _ m s) = 0 := by
    intro m hm s
    have := (jetAlgebra f κ).quasicoherent m
    obtain ⟨n, t, ht⟩ := AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map_basicOpen
      ((jetAlgebra f κ).part m) chart'.isAffineOpen g' s
    have h1 : affineJetSectionsHom ĵ hD ((jetAlgebra f κ).ofPiece _ m
        ((jetAlgebra f κ).sectionsRestrictPiece hDV' m t)) = 0 := by
      rw [← (jetAlgebra f κ).sectionsRestrictHom_ofPiece hDV' m t,
        affineJetSectionsHom_sectionsRestrictHom ĵ hDV' hD hV']
      exact chart'.affineJetSectionsHom_ofPiece_eq_zero_of_forall_coords_eq_zero ĵ hV' hcon hm t
    have h2 : (jetAlgebra f κ).ofPiece _ m ((jetAlgebra f κ).sectionsRestrictPiece hDV' m t) =
        (jetAlgebra f κ).sectionsUnitHom _ (((C.toScheme.presheaf.map (homOfLE hDV').op).hom g') ^ n) *
          (jetAlgebra f κ).ofPiece _ m s := by
      rw [(jetAlgebra f κ).sectionsUnitHom_mul_ofPiece]
      exact congrArg ((jetAlgebra f κ).ofPiece _ m) ht
    rw [h2] at h1
    simp only [map_mul, map_pow] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero n hg'unit)
  -- the `chart`-coordinate `coords (i, q) ∈ S_{q+1}(V)`, restricted to `D`
  have h3 := hkill (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩) (Nat.succ_ne_zero _)
    ((jetAlgebra f κ).sectionsRestrictPiece hDV _ (chart.coords (i, q)))
  rw [← (jetAlgebra f κ).sectionsRestrictHom_ofPiece hDV (jetWeights.{u} X.toVariety.dim κ ⟨(i, q)⟩)
      (chart.coords (i, q)),
    affineJetSectionsHom_sectionsRestrictHom ĵ hDV hD hV,
    ← affineJetCoordAt_eq_affineJetSectionsHom] at h3
  exact h3

/-! ## The transport step, factored out -/

/-- `weightedPointOfCoords` depends only on the tuple. -/
theorem weightedPointOfCoords_congr (Ct : SmoothProjectiveCurve k) (n κ : ℕ)
    {b b' : Fin (n + 1) → Fin κ → Ct.toScheme.functionField} (h : b = b')
    (hne : ∃ i q, b i q ≠ 0) (hne' : ∃ i q, b' i q ≠ 0) :
    weightedPointOfCoords Ct n κ b hne = weightedPointOfCoords Ct n κ b' hne' := by
  subst h; rfl

/-- **`Spec κ(η_{C̃}) → C̃ → C̃₀` is `Spec` of the pullback of rational functions** (read through
the function fields): by `residueFieldCongr_fromSpecResidueField`, `Hom.SpecMap_residueFieldMap_fromSpecResidueField`,
`FiniteCover.SpecMap_residueFieldCongr_residueFieldMap`). -/
theorem FiniteCover.fromSpecResidueField_hom_eq_SpecMap_dominantFunctionFieldMap
    {Ct₀ : SmoothProjectiveCurve k} (η : FiniteCover k Ct₀) :
    haveI : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
    haveI : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
    haveI : AlgebraicGeometry.IsDominant η.hom := inferInstance
    η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫ η.hom =
      AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
        AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) ≫
        AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫
        Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) := by
  have hint₀ : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
  have hint₁ : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
  have hfac : η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫ η.hom =
      AlgebraicGeometry.Spec.map ((Ct₀.toScheme.residueFieldCongr η.hom_genericPoint.symm).hom ≫
        η.hom.residueFieldMap (genericPoint η.source.toScheme)) ≫
        Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) := by
    rw [AlgebraicGeometry.Spec.map_comp, Category.assoc,
      AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField,
      AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [hfac, η.SpecMap_residueFieldCongr_residueFieldMap]
  simp only [Category.assoc]

/-- **The pullback of rational functions along the normalization in `K₂`** is
`K(C̃₀) → K₁ → K₂ →(e⁻¹) K(C̃)` (by `pullbackFunctionHom_apply` and the compatibility `he` of
`exists_normalization_in_extension`). -/
theorem FiniteCover.dominantFunctionFieldMap_eq_of_normalization {Ct₀ : SmoothProjectiveCurve k}
    (η : FiniteCover k Ct₀) (K₁ : Type u) [Field K₁] [Algebra Ct₀.toScheme.functionField K₁]
    (K₂ : Type u) [Field K₂] [Algebra K₁ K₂] (e : η.source.toScheme.functionField ≃+* K₂)
    (he : ∀ ψ : Ct₀.toScheme.functionField,
      e (pullbackFunction η.hom ψ) = algebraMap K₁ K₂ (algebraMap Ct₀.toScheme.functionField K₁ ψ)) :
    haveI : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
    haveI : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
    haveI : AlgebraicGeometry.IsDominant η.hom := inferInstance
    AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom =
      (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁) ≫
        CommRingCat.ofHom (algebraMap K₁ K₂) ≫
        CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField) :
        CommRingCat.of Ct₀.toScheme.functionField ⟶ CommRingCat.of η.source.toScheme.functionField) := by
  have hint₀ : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
  have hint₁ : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
  apply CommRingCat.hom_ext
  ext ψ
  change pullbackFunctionHom η.hom η.hom_genericPoint ψ =
    e.symm (algebraMap K₁ K₂ (algebraMap Ct₀.toScheme.functionField K₁ ψ))
  rw [pullbackFunctionHom_apply]
  exact (e.symm_apply_eq.mpr (he ψ).symm).symm

/-- **The fiber coordinate of `η ≫ ν₀` at the generic point is the weighted point of the transported
affine lift** (Lemma 3.1 of the paper). Data: a jet chart `(V, chart)` over which
`Spec κ(η_{C̃₀}) → C̃₀ → Y_κ^GG` lies
(`hx₀`), with fiber coordinate `x₀`; a finite extension `K₁/K(C̃₀)` (`k`-algebra, compatible: `hsc`)
and a nonzero tuple `a` in `K₁` with `pointOfTuple (a^w) = x₀` base-changed to `K₁` (`hpt`); a further
extension `K₂/K₁` and the normalization `η : C̃ → C̃₀` in `K₂` (`e`, `he`); a tuple `b` on `C̃` with
`b i q = e⁻¹ (a_{(i,q)}^{q+1})` (`hb`). Conclusion: the fiber coordinate of
`Spec κ(η_{C̃}) → C̃ → C̃₀ → Y_κ^GG` in the chart is `weightedPointOfCoords b`.

Proof: by `FiniteCover.fromSpecResidueField_hom_eq_of_normalization`
the morphism is `Spec (K(C̃₀) → K₁ → K₂ →(e⁻¹) K(C̃)) ≫ (Spec κ(η_{C̃₀}) → C̃₀ → Y_κ^GG)` (read through
the function fields), so by `jetChart.fiberCoords_precomp` its fiber coordinate is the same `Spec`
composed with `x₀`; `hpt` identifies `Spec (K(C̃₀) → K₁) ≫ x₀` with `pointOfTuple K₁ (a^w)`, and the
naturality of `pointOfTuple` in the field (`weightedProjectiveSpace.SpecMap_pointOfTuple`, for
`K₁ → K₂` and for the `k`-linear `e⁻¹`; `e⁻¹` is `k`-linear by `he`, `hsc` and
`FiniteCover.pullbackFunctionHom_structureGerm`) gives `pointOfTuple K(C̃) (e⁻¹ (a^w))`, which is
`weightedPointOfCoords b` by `hb`. ∎ -/
theorem fiberCoords_generic_eq_weightedPointOfCoords_of_normalization
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    {Ct₀ : SmoothProjectiveCurve k} (ν₀ : Ct₀.toScheme ⟶ YGG f κ)
    {V : C.toScheme.Opens} (chart : jetChart f κ V)
    (hx₀ : Set.range ((Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) ≫
      YGG.proj f κ).base ⊆ V)
    (K₁ : Type u) [Field K₁] [Algebra k K₁] [Algebra Ct₀.toScheme.functionField K₁]
    (hsc : ∀ r : k, algebraMap k K₁ r = algebraMap Ct₀.toScheme.functionField K₁
      (letI := Ct₀.functionFieldAlgebra; algebraMap k Ct₀.toScheme.functionField r))
    (a : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → K₁) (ha : a ≠ 0)
    (hpt : weightedProjectiveSpace.pointOfTuple k (jetWeights.{u} X.toVariety.dim κ)
        (jetWeights_pos _ _) K₁
        ⟨fun i => a i ^ jetWeights.{u} X.toVariety.dim κ i, fun h => ha (funext fun i =>
          (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp (jetWeights_pos _ _ i))).mp (congrFun h i))⟩
      = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁)) ≫
          (haveI : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
           AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫
            chart.fiberCoords (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) hx₀))
    (K₂ : Type u) [Field K₂] [Algebra K₁ K₂]
    (η : FiniteCover k Ct₀) (e : η.source.toScheme.functionField ≃+* K₂)
    (he : ∀ ψ : Ct₀.toScheme.functionField,
      e (pullbackFunction η.hom ψ) = algebraMap K₁ K₂ (algebraMap Ct₀.toScheme.functionField K₁ ψ))
    (b : Fin (X.toVariety.dim + 1) → Fin κ → η.source.toScheme.functionField)
    (hne : ∃ i q, b i q ≠ 0)
    (hb : ∀ i q, b i q = e.symm (algebraMap K₁ K₂ (a ⟨(i, q)⟩ ^ ((q : ℕ) + 1))))
    (hx : Set.range ((η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫
      η.hom ≫ ν₀) ≫ YGG.proj f κ).base ⊆ V) :
    chart.fiberCoords
        (η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫ η.hom ≫ ν₀) hx
      = weightedPointOfCoords η.source X.toVariety.dim κ b hne := by
  classical
  have hint₀ : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
  have hint₁ : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
  let alg₀ : Algebra k Ct₀.toScheme.functionField := Ct₀.functionFieldAlgebra
  let alg₁ : Algebra k η.source.toScheme.functionField := η.source.functionFieldAlgebra
  let algkK₂ : Algebra k K₂ := ((algebraMap K₁ K₂).comp (algebraMap k K₁)).toAlgebra
  set x₀ : AlgebraicGeometry.Spec (Ct₀.toScheme.residueField (genericPoint Ct₀.toScheme)) ⟶
      weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _) :=
    chart.fiberCoords (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) hx₀
    with hx₀def
  set x₀' : AlgebraicGeometry.Spec (CommRingCat.of Ct₀.toScheme.functionField) ⟶
      weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _) :=
    AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫ x₀ with hx₀'def
  -- step 4
  set g : AlgebraicGeometry.Spec (η.source.toScheme.residueField (genericPoint η.source.toScheme)) ⟶
      AlgebraicGeometry.Spec (Ct₀.toScheme.residueField (genericPoint Ct₀.toScheme)) :=
    AlgebraicGeometry.Spec.map ((Ct₀.toScheme.residueFieldCongr η.hom_genericPoint.symm).hom ≫
      η.hom.residueFieldMap (genericPoint η.source.toScheme)) with hg
  have hfac : η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫ η.hom ≫ ν₀ =
      g ≫ (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) := by
    rw [hg, AlgebraicGeometry.Spec.map_comp]
    simp only [Category.assoc]
    rw [AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField_assoc,
      AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
  have hx' : Set.range ((g ≫ (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀)) ≫
      YGG.proj f κ).base ⊆ V := hfac ▸ hx
  have hg' : g = AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
      AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) ≫
      AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv :=
    η.SpecMap_residueFieldCongr_residueFieldMap
  have hchain := η.dominantFunctionFieldMap_eq_of_normalization K₁ K₂ e he
  have E2 : AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) =
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K₁ K₂)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁)) := by
    rw [hchain, AlgebraicGeometry.Spec.map_comp, AlgebraicGeometry.Spec.map_comp, Category.assoc]
  -- `e⁻¹` is `k`-linear
  have hk : ∀ r : k, (e.symm : K₂ →+* η.source.toScheme.functionField) (algebraMap k K₂ r) =
      algebraMap k η.source.toScheme.functionField r := by
    intro r
    have h1 : algebraMap k K₂ r =
        algebraMap K₁ K₂ (algebraMap Ct₀.toScheme.functionField K₁
          (algebraMap k Ct₀.toScheme.functionField r)) := by
      change algebraMap K₁ K₂ (algebraMap k K₁ r) = _
      rw [hsc r]
    have h2 : (e.symm : K₂ →+* η.source.toScheme.functionField)
        (algebraMap K₁ K₂ (algebraMap Ct₀.toScheme.functionField K₁
          (algebraMap k Ct₀.toScheme.functionField r))) =
        pullbackFunction η.hom (algebraMap k Ct₀.toScheme.functionField r) := by
      rw [RingEquiv.coe_toRingHom]
      exact e.symm_apply_eq.mpr (he _).symm
    rw [h1, h2, ← pullbackFunctionHom_apply η.hom η.hom_genericPoint]
    exact η.pullbackFunctionHom_structureGerm r
  -- the base change of `x₀` to `K₁` is the point of `a^w`
  let va : {v : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → K₁ // v ≠ 0} :=
    ⟨fun i => a i ^ jetWeights.{u} X.toVariety.dim κ i,
      fun h => ha (funext fun i =>
        (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp (jetWeights_pos _ _ i))).mp (congrFun h i))⟩
  have hbc : AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁)) ≫ x₀' =
      weightedProjectiveSpace.pointOfTuple k (jetWeights.{u} X.toVariety.dim κ)
        (jetWeights_pos _ _) K₁ va :=
    hpt.symm
  -- the tuple `b` is the transported `a^w`
  have htuple : jetCoordTuple b hne =
      ⟨fun i => (e.symm : K₂ →+* η.source.toScheme.functionField)
          (algebraMap K₁ K₂ ((va : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → K₁) i)),
        weightedProjectiveSpace.map_tuple_ne_zero (e.symm : K₂ →+* η.source.toScheme.functionField)
          ⟨fun i => algebraMap K₁ K₂ ((va : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → K₁) i),
            weightedProjectiveSpace.map_tuple_ne_zero (algebraMap K₁ K₂) va⟩⟩ := by
    apply Subtype.ext
    funext p
    exact hb p.down.1 p.down.2
  -- assemble (explicit `Eq.trans`: the intermediate morphisms live on
  -- `Spec κ(η_{C̃})` spelled either as `Spec (residueField _)` or as
  -- `Spec (CommRingCat.of ↑(residueField _))`, which `calc`'s `Trans` synthesis does not identify)
  have s1 : chart.fiberCoords
        (η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫ η.hom ≫ ν₀) hx =
      g ≫ x₀ :=
    (chart.fiberCoords_congr hfac hx hx').trans (chart.fiberCoords_precomp g _ hx₀ hx')
  have s2 : g ≫ x₀ = AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
      (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) ≫ x₀') := by
    rw [hg', hx₀'def]
    simp only [Category.assoc]
  have s3 : AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
      (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) ≫ x₀') =
      AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
        ((AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField)) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K₁ K₂)) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁))) ≫ x₀') :=
    congrArg (fun z => AlgebraicGeometry.Spec.map
      η.source.toScheme.functionFieldIsoResidueField.hom ≫ (z ≫ x₀')) E2
  have s4 : AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
        ((AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField)) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K₁ K₂)) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁))) ≫ x₀') =
      AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
        (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField)) ≫
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K₁ K₂)) ≫
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁)) ≫ x₀'))) := by
    simp only [Category.assoc]
  have s5 := congrArg (fun z => AlgebraicGeometry.Spec.map
      η.source.toScheme.functionFieldIsoResidueField.hom ≫
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField)) ≫
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K₁ K₂)) ≫ z))) hbc
  have s6 := congrArg (fun z => AlgebraicGeometry.Spec.map
      η.source.toScheme.functionFieldIsoResidueField.hom ≫
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField)) ≫ z))
      (weightedProjectiveSpace.SpecMap_pointOfTuple k (jetWeights.{u} X.toVariety.dim κ)
        (jetWeights_pos _ _) (algebraMap K₁ K₂) (fun _ => rfl) va)
  have s7 := congrArg (fun z => AlgebraicGeometry.Spec.map
      η.source.toScheme.functionFieldIsoResidueField.hom ≫ z)
      (weightedProjectiveSpace.SpecMap_pointOfTuple k (jetWeights.{u} X.toVariety.dim κ)
        (jetWeights_pos _ _) (e.symm : K₂ →+* η.source.toScheme.functionField) hk
        ⟨fun i => algebraMap K₁ K₂ ((va : ULift.{u} (Fin (X.toVariety.dim + 1) × Fin κ) → K₁) i),
          weightedProjectiveSpace.map_tuple_ne_zero (algebraMap K₁ K₂) va⟩)
  show _ = AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
    weightedProjectiveSpace.pointOfTuple k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _)
      η.source.toScheme.functionField (jetCoordTuple b hne)
  rw [htuple]
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))

/-! ## The two main lemmas -/

/-- **A generic affine representative, in a finite chart family** (Lemma 3.1 of the paper, first
paragraph of the proof of Lemma 3.1 of the paper). Input: a `k`-morphism
`ν₀ : C̃₀ → Y_κ^GG` with `ν₀ ≫ π_κ` finite (instance), surjective and sending the generic point to the
generic point. Output: a finite family of affine honest jet charts `(V α, chart α)` covering `C`,
all containing `η_C`, a designated chart `α₀`; a finite cover `ρ : C̃ → C` factoring as
`ρ = η ≫ ν₀ ≫ π_κ` with `η : C̃ → C̃₀` finite, generic point to generic point; an affine jet
`ĵ : Spec κ(η_{C̃}) → J_κ^s` over `η_{C̃} ≫ ρ` (`hĵ`), lying over every `V α` (`hĵV`); its coordinate
tuples `b α i q = ĵ^♯ ((chart α).coords (i, q))` (`hb`, `affineJetCoord`; weight `q + 1`), each not
identically zero (`hne`) and with `(q+1)`-th roots in `K(C̃)` for every chart (`hroot`); and the fiber
coordinate of `η ≫ ν₀` at the generic point of `C̃` in the chart `α₀` is the weighted point of
`b α₀` (`weightedPointOfCoords`). These are exactly the hypotheses of `exists_basedJet_of_affineJet`
(`BasedJetOfChartFamily`) plus the link to `ν₀`.

Proof (formalized below; every step names its lemma):
1. `HonestJetChart.exists_finite_cover`: the finite family `(V α, chart α)`, `hηV`, `hcover`; `α₀` any
   index (`hcover` at `η_C`).
2. `x₀ := (chart α₀).fiberCoords (Spec κ(η_{C̃₀}) → C̃₀ → Y_κ^GG)` is a `k`-morphism
   (`jetChart.fiberCoords_over`); transported to `Spec K(C̃₀)` it is a `KPoint k w K(C̃₀)` `X₀` for
   `functionFieldAlgebra` (`SpecMap_functionFieldIsoResidueField_inv_fromSpecResidueField`,
   `SpecMap_algebraMap_functionFieldAlgebra`).
3. `exists_affine_lift_of_weighted_point` (the paper's finite
   surjective map `P^{(n+1)κ-1} → P(1^{n+1},…,κ^{n+1})`, Lemma 3.1 of the paper): a finite extension
   `K₁/K(C̃₀)` and a nonzero tuple `a` with `pointOfTuple K₁ (a^w) = X₀.baseChange K₁`.
4. **The affine jet over `K₁`** (Lemma 3.1 of the paper): `y₁ : Spec K₁ → Spec K(C̃₀) → C̃₀ → C` lands
   at `η_C ∈ V α₀`; `HonestJetChart.exists_affineJet_of_tuple`
   gives `ĵ₁ : Spec K₁ → J_κ^s` over `y₁` with `α₀`-coordinates `a_{(i,q)}^{q+1}`. It lies over every
   `V α` (its image in `C` is `η_C`). Put `v₁ α i q := affineJetCoordAt ĵ₁ ((chart α).coords (i,q))`
   (the paper's `b_{α,i,q}`, Lemma 3.1 of the paper).
5. **Roots simultaneously for all charts** (Lemma 3.1 of the paper):
   `exists_finite_extension_with_roots`  for the finitely many
   `v₁ α i q` (`ι × Fin (n+1) × Fin κ` is finite) gives `K₂/K₁` finite and `c` with
   `c_{α,i,q}^{q+1} = v₁ α i q`; `K₂/K(C̃₀)` is finite (`Module.Finite.trans`).
6. `exists_normalization_in_extension` : the finite cover
   `η : C̃ → C̃₀` with `e : K(C̃) ≃+* K₂` compatible with pullback of functions.
   `ρ := η ≫ ν₀ ≫ π_κ` is a `FiniteCover k C` (finite, surjective, over `k`, as in `weighted_rescaling`).
7. `ĵ := Spec (K₁ → K₂ →(e⁻¹) K(C̃) ≅ κ(η_{C̃}))⁻¹ ≫ ĵ₁`, i.e. `Spec.map ffIso.hom ≫ Spec.map e⁻¹ ≫
   Spec.map (K₁ → K₂) ≫ ĵ₁`. `hĵ`: by `FiniteCover.fromSpecResidueField_hom_eq_of_normalization`,
   `Spec κ(η_{C̃}) → C̃ → C̃₀` is `Spec.map ffIso.hom ≫ Spec.map e⁻¹ ≫ Spec.map (K₁ → K₂) ≫
   Spec.map (K(C̃₀) → K₁) ≫ Spec.map ffIso₀⁻¹ ≫ (Spec κ(η_{C̃₀}) → C̃₀)`, and `ĵ₁ ≫ π = y₁`. `hĵV`: the
   image of `ĵ ≫ π` is `ρ(η_{C̃}) = η_C ∈ V α`.
8. `b α i q := affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i,q))` (`hb` by definition). By
   `affineJetCoordAt_SpecMap_comp` (three times) `b α i q = e⁻¹ (v₁ α i q)` (as elements of `K(C̃)`,
   through `K₁ → K₂`); so `hroot` is `e⁻¹ c_{α,i,q}`; `hne α₀` is `a ≠ 0` (step 4); `hne α` for the
   other charts is `HonestJetChart.exists_affineJetCoordAt_ne_zero_of_exists_ne_zero`
    applied to `ĵ₁`.
9. The fiber coordinate: `fiberCoords_generic_eq_weightedPointOfCoords_of_normalization` with
   `b α₀ i q = e⁻¹ (a_{(i,q)}^{q+1})` (steps 4 and 8). ∎

Edge cases: `κ = 0` — `Y_0^GG` is empty, so `ν₀` cannot exist unless `C̃₀` is empty (it is not);
`hκ` records this and is unused. `n = 0` fine. -/
theorem weighted_rescaling_generic_affineJet [IsAlgClosed k] [CharZero k]
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (_hκ : 1 ≤ κ)
    {Ct₀ : SmoothProjectiveCurve k} (ν₀ : Ct₀.toScheme ⟶ YGG f κ)
    [ν₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsFinite (ν₀ ≫ YGG.proj f κ)]
    (hsurj : Function.Surjective (ν₀ ≫ YGG.proj f κ).base)
    (hgen : (ν₀ ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → C.toScheme.Opens)
      (_ : ∀ α, AlgebraicGeometry.IsAffineOpen (V α)) (chart : ∀ α, HonestJetChart f κ (V α))
      (_ : ∀ α, genericPoint C.toScheme ∈ V α) (_ : ∀ c : C.toScheme, ∃ α, c ∈ V α) (α₀ : ι)
      (ρ : FiniteCover k C) (η : ρ.source.toScheme ⟶ Ct₀.toScheme)
      (_ : AlgebraicGeometry.IsFinite η)
      (_ : η.base (genericPoint ρ.source.toScheme) = genericPoint Ct₀.toScheme)
      (_ : ρ.hom = η ≫ ν₀ ≫ YGG.proj f κ)
      (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
        (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
      (_ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
        ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
      (hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
          (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
        ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
          ⁻¹ᵁ V α))
      (b : ι → Fin (X.toVariety.dim + 1) → Fin κ → ρ.source.toScheme.functionField)
      (_ : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ),
        b α i q = affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i, q)))
      (hne : ∀ α, ∃ i q, b α i q ≠ 0)
      (_ : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), b α i q ≠ 0 →
        ∃ c : ρ.source.toScheme.functionField, c ^ ((q : ℕ) + 1) = b α i q)
      (hx : Set.range ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫
        η ≫ ν₀) ≫ YGG.proj f κ).base ⊆ V α₀),
      (chart α₀).fiberCoords
          (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ η ≫ ν₀) hx
        = weightedPointOfCoords ρ.source X.toVariety.dim κ (b α₀) (hne α₀) := by
  classical
  have hint₀ : AlgebraicGeometry.IsIntegral Ct₀.toScheme := Ct₀.isIntegral
  have hintC : AlgebraicGeometry.IsIntegral C.toScheme := C.isIntegral
  let alg₀ : Algebra k Ct₀.toScheme.functionField := Ct₀.functionFieldAlgebra
  -- Step 1: the finite honest chart family
  obtain ⟨ι, hfin, V, hV, chart, hηV, hcover⟩ := HonestJetChart.exists_finite_cover f κ
  obtain ⟨α₀, -⟩ := hcover (genericPoint C.toScheme)
  -- Step 2: the fiber coordinate `x₀` of `ν₀` at the generic point, as a `KPoint` over `K(C̃₀)`
  have hgen' : (YGG.proj f κ).base (ν₀.base (genericPoint Ct₀.toScheme)) = genericPoint C.toScheme :=
    hgen
  have hx₀ : Set.range ((Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) ≫
      YGG.proj f κ).base ⊆ V α₀ := by
    rintro _ ⟨s, rfl⟩
    show (YGG.proj f κ).base (ν₀.base
      ((Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme)).base s)) ∈ V α₀
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply, hgen']
    exact hηV α₀
  set x₀ : AlgebraicGeometry.Spec (Ct₀.toScheme.residueField (genericPoint Ct₀.toScheme)) ⟶
      weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _) :=
    (chart α₀).fiberCoords (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) hx₀
    with hx₀def
  set x₀' : AlgebraicGeometry.Spec (CommRingCat.of Ct₀.toScheme.functionField) ⟶
      weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _) :=
    AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫ x₀ with hx₀'def
  have hx₀'over : x₀' ≫ (weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ)
      (jetWeights_pos _ _) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k Ct₀.toScheme.functionField)) := by
    have h1 : x₀ ≫ (weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _)
        ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) ≫
          (YGG f κ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      (chart α₀).fiberCoords_over _ hx₀
    have h2 : (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀) ≫
        (YGG f κ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫
          (Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      rw [Category.assoc, (inferInstance : ν₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1]
    have h3 : AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫
        Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) =
        Ct₀.toScheme.fromSpecStalk (genericPoint Ct₀.toScheme) :=
      Ct₀.toScheme.SpecMap_functionFieldIsoResidueField_inv_fromSpecResidueField
    calc x₀' ≫ (weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _)
          ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        = AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫
            (x₀ ≫ (weightedProjectiveSpace k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _)
              ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := Category.assoc _ _ _
      _ = AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫
            (Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫
              (Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :=
          congrArg (fun z => AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫ z)
            (h1.trans h2)
      _ = (AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫
            Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme)) ≫
              (Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := (Category.assoc _ _ _).symm
      _ = Ct₀.toScheme.fromSpecStalk (genericPoint Ct₀.toScheme) ≫
            (Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
          congrArg (fun z => z ≫ (Ct₀.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) h3
      _ = _ := Ct₀.SpecMap_algebraMap_functionFieldAlgebra.symm
  let X₀ : weightedProjectiveSpace.KPoint k (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _)
      Ct₀.toScheme.functionField := ⟨x₀', hx₀'over⟩
  -- Step 3: the affine lift after a finite extension `K₁`
  obtain ⟨K₁, _, _, _, _, _, a, ha, hpt⟩ :=
    exists_affine_lift_of_weighted_point (jetWeights.{u} X.toVariety.dim κ) (jetWeights_pos _ _) X₀
  have hsc : ∀ r : k, algebraMap k K₁ r = algebraMap Ct₀.toScheme.functionField K₁
      (algebraMap k Ct₀.toScheme.functionField r) := fun r =>
    IsScalarTower.algebraMap_apply k Ct₀.toScheme.functionField K₁ r
  -- Step 4: the affine jet `ĵ₁` over `K₁` with `α₀`-coordinates `a^w`
  let y₁ : AlgebraicGeometry.Spec (CommRingCat.of K₁) ⟶ C.toScheme :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁)) ≫
      AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv ≫
      Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme) ≫ ν₀ ≫ YGG.proj f κ
  have hy₁gen : ∀ s, y₁.base s = genericPoint C.toScheme := by
    intro s
    show (YGG.proj f κ).base (ν₀.base
      ((Ct₀.toScheme.fromSpecResidueField (genericPoint Ct₀.toScheme)).base
        ((AlgebraicGeometry.Spec.map Ct₀.toScheme.functionFieldIsoResidueField.inv).base
          ((AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁))).base s)))) =
      genericPoint C.toScheme
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply, hgen']
  have hy₁ : Set.range y₁.base ⊆ V α₀ := by
    rintro _ ⟨s, rfl⟩
    rw [hy₁gen]
    exact hηV α₀
  obtain ⟨ĵ₁, hĵ₁, hĵ₁V₀, hcoord₁⟩ :=
    (chart α₀).exists_affineJet_of_tuple y₁ hy₁ (fun i q => a ⟨(i, q)⟩ ^ ((q : ℕ) + 1))
  have hĵ₁V : ∀ α, (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of K₁)).Opens) ≤
      ĵ₁ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α) := by
    intro α s _
    show (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.base
      (ĵ₁.base s) ∈ V α
    have : (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.base
        (ĵ₁.base s) = y₁.base s :=
      congrArg (fun m => m.base s) hĵ₁
    rw [this, hy₁gen]
    exact hηV α
  let v₁ : ι → Fin (X.toVariety.dim + 1) → Fin κ → K₁ := fun α i q =>
    affineJetCoordAt ĵ₁ (hĵ₁V α) _ ((chart α).coords (i, q))
  have hv₁ : ∀ i q, v₁ α₀ i q = a ⟨(i, q)⟩ ^ ((q : ℕ) + 1) := fun i q => hcoord₁ i q
  -- Step 5: roots for all charts simultaneously, in `K₂`
  obtain ⟨K₂, _, _, _, c, hc⟩ := exists_finite_extension_with_roots (K := K₁)
    (ι := ι × Fin (X.toVariety.dim + 1) × Fin κ) (fun p => v₁ p.1 p.2.1 p.2.2)
    (fun p => (p.2.2 : ℕ) + 1) (fun p => Nat.succ_pos _)
  let algK₀K₂ : Algebra Ct₀.toScheme.functionField K₂ :=
    ((algebraMap K₁ K₂).comp (algebraMap Ct₀.toScheme.functionField K₁)).toAlgebra
  have : IsScalarTower Ct₀.toScheme.functionField K₁ K₂ :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Finite Ct₀.toScheme.functionField K₂ := Module.Finite.trans K₁ K₂
  -- Step 6: the normalization `η : C̃ → C̃₀` in `K₂`, and `ρ`
  obtain ⟨Ct₁, η, -, e, he⟩ := exists_normalization_in_extension Ct₀ K₂
  have hint₁ : AlgebraicGeometry.IsIntegral η.source.toScheme := η.source.isIntegral
  have he' : ∀ ψ : Ct₀.toScheme.functionField,
      e (pullbackFunction η.hom ψ) = algebraMap K₁ K₂ (algebraMap Ct₀.toScheme.functionField K₁ ψ) :=
    fun ψ => he ψ
  have : AlgebraicGeometry.Surjective (ν₀ ≫ YGG.proj f κ) := ⟨hsurj⟩
  let ρ : FiniteCover k C :=
    { source := η.source
      hom := η.hom ≫ ν₀ ≫ YGG.proj f κ
      isOver := by
        simp only [Category.assoc]
        change η.hom ≫ ν₀ ≫ (YGG f κ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) = _
        rw [(inferInstance : ν₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1]
        exact η.isOver }
  have hηg : η.hom.base (genericPoint η.source.toScheme) = genericPoint Ct₀.toScheme :=
    η.hom_genericPoint
  -- Step 7: the affine jet `ĵ` over `κ(η_{C̃})`
  let e' : CommRingCat.of K₂ ⟶ CommRingCat.of η.source.toScheme.functionField :=
    CommRingCat.ofHom (e.symm : K₂ →+* η.source.toScheme.functionField)
  let ι' : CommRingCat.of K₁ ⟶ CommRingCat.of K₂ := CommRingCat.ofHom (algebraMap K₁ K₂)
  let ι₀ : CommRingCat.of Ct₀.toScheme.functionField ⟶ CommRingCat.of K₁ :=
    CommRingCat.ofHom (algebraMap Ct₀.toScheme.functionField K₁)
  let ĵ₂ : AlgebraicGeometry.Spec (CommRingCat.of K₂) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left :=
    AlgebraicGeometry.Spec.map ι' ≫ ĵ₁
  let ĵ₃ : AlgebraicGeometry.Spec (CommRingCat.of η.source.toScheme.functionField) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left :=
    AlgebraicGeometry.Spec.map e' ≫ ĵ₂
  let ĵ : AlgebraicGeometry.Spec (η.source.toScheme.residueField (genericPoint η.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left :=
    AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫ ĵ₃
  have E2 : AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap η.hom) =
      AlgebraicGeometry.Spec.map e' ≫ AlgebraicGeometry.Spec.map ι' ≫ AlgebraicGeometry.Spec.map ι₀ := by
    rw [η.dominantFunctionFieldMap_eq_of_normalization K₁ K₂ e he', AlgebraicGeometry.Spec.map_comp,
      AlgebraicGeometry.Spec.map_comp, Category.assoc]
  have hA := η.fromSpecResidueField_hom_eq_SpecMap_dominantFunctionFieldMap
  have hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫ ρ.hom := by
    change (AlgebraicGeometry.Spec.map η.source.toScheme.functionFieldIsoResidueField.hom ≫
        (AlgebraicGeometry.Spec.map e' ≫ (AlgebraicGeometry.Spec.map ι' ≫ ĵ₁))) ≫
        (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫ η.hom ≫ ν₀ ≫ YGG.proj f κ
    rw [← Category.assoc (η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme)) η.hom,
      hA, E2]
    simp only [Category.assoc, hĵ₁, y₁, ι₀]
  have hĵV : ∀ α, (⊤ : (AlgebraicGeometry.Spec
      (η.source.toScheme.residueField (genericPoint η.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α) := by
    intro α s _
    show (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.base
      (ĵ.base s) ∈ V α
    have h1 : (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.base
        (ĵ.base s) = ρ.hom.base
          ((η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme)).base s) :=
      congrArg (fun m => m.base s) hĵ
    rw [h1, AlgebraicGeometry.Scheme.fromSpecResidueField_apply]
    change (YGG.proj f κ).base (ν₀.base (η.hom.base (genericPoint η.source.toScheme))) ∈ V α
    rw [hηg, hgen']
    exact hηV α
  -- Step 8: the coordinate tuples `b α`, their roots and non-vanishing
  let b : ι → Fin (X.toVariety.dim + 1) → Fin κ → η.source.toScheme.functionField :=
    fun α i q => affineJetCoord ρ ĵ (hĵV α) _ ((chart α).coords (i, q))
  have hĵ₂V : ∀ α, (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of K₂)).Opens) ≤
      ĵ₂ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α) := fun α => top_le_preimage_comp_of_top_le _ _ (hĵ₁V α)
  have hĵ₃V : ∀ α, (⊤ : (AlgebraicGeometry.Spec
      (CommRingCat.of η.source.toScheme.functionField)).Opens) ≤
      ĵ₃ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V α) := fun α => top_le_preimage_comp_of_top_le _ _ (hĵ₂V α)
  have hbval : ∀ α i q, b α i q = e.symm (algebraMap K₁ K₂ (v₁ α i q)) := by
    intro α i q
    have h3 : affineJetCoordAt ĵ₂ (hĵ₂V α) _ ((chart α).coords (i, q)) = ι'.hom (v₁ α i q) :=
      affineJetCoordAt_SpecMap_comp ι' ĵ₁ (hĵ₁V α) (hĵ₂V α) _ _
    have h2 : affineJetCoordAt ĵ₃ (hĵ₃V α) _ ((chart α).coords (i, q)) =
        e'.hom (affineJetCoordAt ĵ₂ (hĵ₂V α) _ ((chart α).coords (i, q))) :=
      affineJetCoordAt_SpecMap_comp e' ĵ₂ (hĵ₂V α) (hĵ₃V α) _ _
    have h1 : affineJetCoordAt ĵ (hĵV α) _ ((chart α).coords (i, q)) =
        η.source.toScheme.functionFieldIsoResidueField.hom.hom
          (affineJetCoordAt ĵ₃ (hĵ₃V α) _ ((chart α).coords (i, q))) :=
      affineJetCoordAt_SpecMap_comp η.source.toScheme.functionFieldIsoResidueField.hom ĵ₃ (hĵ₃V α)
        (hĵV α) _ _
    show η.source.toScheme.functionFieldIsoResidueField.inv.hom
      (affineJetCoordAt ĵ (hĵV α) _ ((chart α).coords (i, q))) = _
    rw [h1, h2, h3]
    exact CommRingCat.inv_hom_apply η.source.toScheme.functionFieldIsoResidueField _
  have hroot : ∀ α (i : Fin (X.toVariety.dim + 1)) (q : Fin κ), b α i q ≠ 0 →
      ∃ c' : η.source.toScheme.functionField, c' ^ ((q : ℕ) + 1) = b α i q := by
    intro α i q _
    refine ⟨e.symm (c (α, i, q)), ?_⟩
    rw [hbval, ← map_pow]
    exact congrArg e.symm (hc (α, i, q))
  have hne₀ : ∃ i q, v₁ α₀ i q ≠ 0 := by
    obtain ⟨p, hp⟩ : ∃ p, a p ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    refine ⟨p.down.1, p.down.2, ?_⟩
    rw [hv₁]
    exact pow_ne_zero _ hp
  have hne : ∀ α, ∃ i q, b α i q ≠ 0 := by
    intro α
    obtain ⟨i, q, hiq⟩ := (chart α₀).exists_affineJetCoordAt_ne_zero_of_exists_ne_zero ĵ₁ (chart α)
      (hĵ₁V α₀) (hĵ₁V α) hne₀
    refine ⟨i, q, ?_⟩
    rw [hbval]
    exact fun h0 => hiq ((map_eq_zero _).mp (e.symm.injective (h0.trans (map_zero _).symm)))
  -- Step 9: the fiber coordinate of `η ≫ ν₀` in the chart `α₀`
  have hx : Set.range ((η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme) ≫
      η.hom ≫ ν₀) ≫ YGG.proj f κ).base ⊆ V α₀ := by
    rintro _ ⟨s, rfl⟩
    show (YGG.proj f κ).base (ν₀.base (η.hom.base
      ((η.source.toScheme.fromSpecResidueField (genericPoint η.source.toScheme)).base s))) ∈ V α₀
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply, hηg, hgen']
    exact hηV α₀
  refine ⟨ι, hfin, V, hV, chart, hηV, hcover, α₀, ρ, η.hom, η.finite, hηg, rfl, ĵ, hĵ, hĵV, b,
    fun _ _ _ => rfl, hne, hroot, hx, ?_⟩
  exact fiberCoords_generic_eq_weightedPointOfCoords_of_normalization f κ ν₀ (chart α₀).tojetChart
    hx₀ K₁ hsc a ha hpt K₂ η e he' (b α₀) (hne α₀)
    (fun i q => by rw [hbval, hv₁]) hx

end
