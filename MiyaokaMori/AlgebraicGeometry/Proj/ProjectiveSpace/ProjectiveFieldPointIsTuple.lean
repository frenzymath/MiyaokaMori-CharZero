import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTuplePoint
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveChartRingHomExt

/-! # Every field-valued point of `P^N_k` is the point of a tuple

Every field-valued point of `P^N_k` (a `k`-morphism `Spec K → P^N_k`) is the point `[f_0 : … : f_N]` of
some nonzero tuple `f`.

Source: Hartshorne II Thm 7.1(a) with `X = Spec K` (every line bundle is trivial); Debarre, Introduction to
Mori theory, 2.18.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectiveSpace

/-- `X_j / X_j = 1` in the chart ring `k[X]_{(X_j)}` (checked on `val` in `Localization.Away (X_j)`). -/
theorem ratioElement_self {k : Type u} [Field k] {N : ℕ} (j : Fin (N + 1)) :
    ProjectiveSpaceOverChart.ratioElement (R := k) N j j = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [ProjectiveSpaceOverChart.ratioElement, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  simp only [pow_one]
  exact Localization.mk_self (S := Submonoid.powers (MvPolynomial.X (R := k) j))
    ⟨MvPolynomial.X j, Submonoid.mem_powers _⟩

/-- The evaluation homomorphism of a tuple at the variable `X_i` is (the image under `ΓSpecIso⁻¹` of)
the `i`-th coordinate. -/
theorem tupleEval_X (k : Type u) [Field k] (N : ℕ) (R : Type u) [CommRing R] (c : k →+* R)
    (b : Fin (N + 1) → R) (i : Fin (N + 1)) :
    ProjectiveSpace.tupleEval k N R c b (MvPolynomial.X i) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (b i) := by
  simp [ProjectiveSpace.tupleEval]

/-- The evaluation homomorphism of a tuple at a constant `C a` is (the image under `ΓSpecIso⁻¹` of)
`c a`. -/
theorem tupleEval_C (k : Type u) [Field k] (N : ℕ) (R : Type u) [CommRing R] (c : k →+* R)
    (b : Fin (N + 1) → R) (a : k) :
    ProjectiveSpace.tupleEval k N R c b (MvPolynomial.C a) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c a) := by
  simp [ProjectiveSpace.tupleEval]

end ProjectiveSpace

/-- Every `k`-morphism `x : Spec K → P^N_k` is `tuplePoint k N K c f hf` for some tuple `f : Fin (N+1) → K`
generating the unit ideal.

Proof. `Spec K` has a single point `pt`. The standard opens `D_+(X_j)` (`j : Fin (N+1)`) cover `P^N`
(`Proj.iSup_basicOpen_eq_top'`; the `X_j` generate the irrelevant ideal); choose `j` with `x pt ∈ D_+(X_j)`.
Then `x` factors through the open immersion `Proj.awayι 𝒜 (X j) _ _ : Spec (Away 𝒜 (X j)) → Proj 𝒜`
(`IsOpenImmersion.lift`; the range condition holds since there is one point), giving `ρ : Away 𝒜 (X j) →+* K`
with `x = Spec.map ρ ≫ awayι` (`Spec.preimage` / `Spec.map_preimage`).
Put `f_i := ρ (ratioElement N i j)`; then `f_j = ρ 1 = 1`, so `f` generates the unit ideal.
By `ProjectiveSpaceOverChart.chartMap_ι`,
`chartMap (Spec K) N e j hj ≫ (D_+(X_j)).ι = Proj.fromOfGlobalSections 𝒜 e he` (with `e := tupleEval k N K c f`),
where `chartMap` is given by the ring homomorphism `chartEvaluation N e j hj : Away → Γ(Spec K, ⊤)`;
`chartEvaluation_ratio_mul` gives `chartEvaluation(ratio i j) · e(X_j) = e(X_i)`, i.e. `= ΓSpecIso.inv (f_i)`
(as `e(X_j) = 1`). By `ProjectiveSpace.chartRingHom_ext`, `chartEvaluation = ΓSpecIso.inv ∘ ρ` (agreement on
`k` comes from `hx : x ≫ (P^N ↘ Spec k) = Spec.map c`), so the two morphisms `Spec K → D_+(X_j)` agree, and
composing with `ι` gives `x = tuplePoint`.

Details. Use of `hx`: from `x = Spec.map ρ ≫ awayι`, `Proj.awayι_toSpecZero` rewrites `awayι ≫ toSpecZero` as
`Spec.map (fromZeroRingHom)`, and `Spec.map_injective` gives `ρ ∘ fromZeroRingHom ∘ algebraMap k 𝒜₀ = c`.
The value of `chartEvaluation` at `fromZeroRingHom (algebraMap a)`: `val = mk' (C a) 1 = algebraMap (C a)`
(`IsLocalization.mk'_one`), then `IsLocalization.Away.lift_eq` gives `e (C a) = ΓSpecIso.inv (c a)` (`tupleEval_C`).
The degree proof for `Proj.awayι` must be given as `X j ∈ 𝒜 1` (`hXj`) rather than `isHomogeneous_X`, otherwise
instance search / `rw` cannot unify the implicit degree `m`.
Edge case: for `N = 0`, `Fin 1` has a single coordinate, `f_0 = 1` and the conclusion is trivial; the proof does
not distinguish this case. `K` is a field, so `Spec K` is nonempty with a single point. -/
theorem ProjectiveSpace.exists_tuplePoint_of_field (k : Type u) [Field k] (N : ℕ) (K : Type u)
    [Field K] (c : k →+* K) (x : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ ProjectiveSpace N k)
    (hx : x ≫ (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom c)) :
    ∃ (f : Fin (N + 1) → K) (hf : Ideal.span (Set.range f) = ⊤),
      x = ProjectiveSpace.tuplePoint k N K c f hf := by
  classical
  -- Step 1: the image of the (unique) point of `Spec K` lies in some chart `D₊(X_j)`.
  have hcover : ⨆ j, AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
      (MvPolynomial.X j) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' _ MvPolynomial.X
      (fun i => ⟨1, MvPolynomial.isHomogeneous_X k i⟩) ProjectiveSpace.adjoin_gradeZero_range_X
  let pt : AlgebraicGeometry.Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hmem : (x.base pt : AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N)) ∈
      (⊤ : (AlgebraicGeometry.Proj (AlgebraicGeometry.Proj.projectiveGrading k N)).Opens) := trivial
  rw [← hcover] at hmem
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  -- Step 2: lift `x` through the open immersion `awayι`.
  have hXj : MvPolynomial.X j ∈ (AlgebraicGeometry.Proj.projectiveGrading k N) 1 := MvPolynomial.isHomogeneous_X k j
  set ι := AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X j)
    hXj Nat.zero_lt_one with hι
  have : AlgebraicGeometry.IsOpenImmersion ι := inferInstanceAs (AlgebraicGeometry.IsOpenImmersion
    (AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X j)
      hXj Nat.zero_lt_one))
  have hrange : Set.range x.base ⊆ Set.range ι.base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = pt := Subsingleton.elim _ _
    rw [hp]
    rw [← AlgebraicGeometry.Proj.opensRange_awayι (AlgebraicGeometry.Proj.projectiveGrading k N)
      (MvPolynomial.X j) hXj Nat.zero_lt_one] at hj
    exact hj
  let φ := AlgebraicGeometry.IsOpenImmersion.lift ι x hrange
  have hφ : φ ≫ ι = x := AlgebraicGeometry.IsOpenImmersion.lift_fac ι x hrange
  let ρ : HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X j) →+* K :=
    (AlgebraicGeometry.Spec.preimage φ).hom
  have hρ : AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ) = φ := by
    simp [ρ]
  -- Step 3: the tuple.
  let f : Fin (N + 1) → K := fun i => ρ (ProjectiveSpaceOverChart.ratioElement N i j)
  have hfj : f j = 1 := by
    simp only [f, ProjectiveSpace.ratioElement_self, map_one]
  have hf : Ideal.span (Set.range f) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (hfj ▸ Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨f, hf, ?_⟩
  -- Step 4: compare with `tuplePoint` through the chart.
  let e := ProjectiveSpace.tupleEval k N K c f
  have heXj : e (MvPolynomial.X j) = 1 := by
    simp only [e, ProjectiveSpace.tupleEval_X, hfj, map_one]
  have hju : IsUnit (e (MvPolynomial.X j)) := by rw [heXj]; exact isUnit_one
  have hchart := ProjectiveSpaceOverChart.chartMap_ι
    (AlgebraicGeometry.Spec (CommRingCat.of K)) N e
    (ProjectiveSpace.tupleEval_irrelevant k N K c f hf) j hju
  change x = AlgebraicGeometry.Proj.fromOfGlobalSections _ e _
  rw [← hchart]
  simp only [ProjectiveSpaceOverChart.chartMap, Category.assoc]
  rw [AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι (AlgebraicGeometry.Proj.projectiveGrading k N)
    (MvPolynomial.X j) hXj Nat.zero_lt_one]
  rw [← hφ, ← hρ, ← AlgebraicGeometry.SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_comp_assoc]
  congr 2
  -- reduce to an equality of ring homs out of the chart ring
  have hk_eq : (ρ.comp (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k N)
      (Submonoid.powers (MvPolynomial.X j)))).comp
        (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0)) = c := by
    have h1 : x ≫ (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ) ≫
          (AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X j)
            hXj Nat.zero_lt_one ≫
          (AlgebraicGeometry.Proj.toSpecZero (AlgebraicGeometry.Proj.projectiveGrading k N) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom
              (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0))))) := by
      rw [← hι, hρ, ← Category.assoc, hφ]; rfl
    rw [h1, AlgebraicGeometry.Proj.awayι_toSpecZero_assoc, ← AlgebraicGeometry.Spec.map_comp,
      ← AlgebraicGeometry.Spec.map_comp] at hx
    have h2 := AlgebraicGeometry.Spec.map_injective hx
    have h3 := congrArg CommRingCat.Hom.hom h2
    simpa using h3
  have hcomp : (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp ρ =
      ProjectiveSpaceOverChart.chartEvaluation N e j hju := by
    apply ProjectiveSpace.chartRingHom_ext j
    · intro a
      have hL : ρ (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k N) _
          (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0) a)) = c a := by
        have := congrArg (fun φ => φ a) hk_eq
        simpa using this
      have hR : ProjectiveSpaceOverChart.chartEvaluation N e j hju
          (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k N) _
            (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0) a)) =
          e (MvPolynomial.C a) := by
        simp only [ProjectiveSpaceOverChart.chartEvaluation, RingHom.comp_apply,
          HomogeneousLocalization.algebraMap_apply]
        have hval : (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k N)
            (Submonoid.powers (MvPolynomial.X j))
            (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k N) 0) a)).val =
            algebraMap (MvPolynomial (Fin (N + 1)) k)
              (Localization.Away (MvPolynomial.X (R := k) j)) (MvPolynomial.C a) := by
          change (HomogeneousLocalization.mk _).val = _
          rw [HomogeneousLocalization.val_mk]
          simp only [Localization.mk_eq_mk']
          exact IsLocalization.mk'_one _ _
        rw [hval, IsLocalization.Away.lift_eq]
      rw [RingHom.comp_apply, hL, hR, ProjectiveSpace.tupleEval_C]
    · intro i
      have h := ProjectiveSpaceOverChart.chartEvaluation_ratio_mul N e j hju i
      rw [heXj, mul_one, ProjectiveSpace.tupleEval_X] at h
      rw [RingHom.comp_apply, h]
  -- conclude
  ext1
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rw [← hcomp, ← RingHom.comp_assoc]
  have : (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom = RingHom.id _ := by
    ext a
    simp
  rw [this, RingHom.id_comp]

end
