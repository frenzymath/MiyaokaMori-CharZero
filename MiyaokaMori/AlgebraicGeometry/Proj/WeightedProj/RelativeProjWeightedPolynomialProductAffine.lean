import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.RelativeProjWeightedPolynomialProductAffineSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjWeightedPolynomialProductAffineProjIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistChartIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjMapToSpecZero

/-! # Relative Proj of the weighted polynomial algebra over `Spec k`

Affine base case of `relativeProj_weightedPolynomialAlgebra_iso`: over `Spec k` the relative
Proj of the weighted polynomial algebra `weightedPolynomialQCAlgebra (Spec k) w hw` is the weighted
projective space `P_k(w)` (compatibly with the structure morphisms to `Spec k`), and
`O(m)` corresponds to `weightedProjTwist k w hw m`.

References: Stacks 01NQ (relative Proj over an affine open is Proj of the sections),
01NR (the twists correspond), 01MM/01MX (the twist along `Proj.map` of a graded ring
isomorphism).

The route (see the theorem docstring) is:
1. `Proj_X S ≅ Proj A` (`A = Γ(⊤, S)`): the chart square `projChart ⊤` is a pullback along the
   isomorphism `⊤.ι` (`GradedAffineAlgebra.projChart_isPullback`, Stacks 01NQ), so `projChart ⊤` is an
   isomorphism.
2. `A ≃+* k[x_σ]` as graded rings with unit compatibility: the sections of the free sheaves on the
   finite monomial index sets (`sectionsRingEquiv`) composed with `ΓSpecIso`.
3. `Proj A ≅ P_k(w)` by `Proj.isoOfGradedRingEquiv`; compatibility with the structure maps by
   `proj_map_toSpecZero` and the unit compatibility of step 2.
4. Twists: `twistChartHom` is an isomorphism (`GradedAffineAlgebra.isIso_twistChartHom`, Stacks 01LI),
   and θ along the graded ring isomorphism is an isomorphism
   (`Proj.isIso_twistPullbackHom_gradedRingHomOfRingEquivSymm`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace RelativeProjWeightedPolynomialSpec

open AlgebraicGeometry AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)

/-- The graded sections ring of the weighted polynomial algebra over `Spec k` is `k[x_σ]`
(`sectionsRingEquiv` followed by `ΓSpecIso : Γ(Spec k, ⊤) ≅ k`). -/
def specRingEquiv :
    (Scheme.weightedPolynomialQCAlgebra (Spec (CommRingCat.of k)) w hw).sectionsRing ⊤ ≃+*
      MvPolynomial σ k :=
  (sectionsRingEquiv w hw ⊤).trans
    (MvPolynomial.mapEquiv σ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv)

theorem specRingEquiv_apply (a : (Scheme.weightedPolynomialQCAlgebra (Spec (CommRingCat.of k)) w hw).sectionsRing ⊤) :
    specRingEquiv k w hw a =
      MvPolynomial.map ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv : Γ(Spec (CommRingCat.of k), ⊤) →+* k)
        (sectionsRingEquiv w hw ⊤ a) := rfl

/-- `MvPolynomial.map` along an injective ring homomorphism preserves and reflects weighted
homogeneity (the coefficients are mapped injectively, so the support is unchanged). -/
theorem isWeightedHomogeneous_map_iff {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f) (p : MvPolynomial σ R) (m : ℕ) :
    (MvPolynomial.map f p).IsWeightedHomogeneous w m ↔ p.IsWeightedHomogeneous w m := by
  simp only [MvPolynomial.IsWeightedHomogeneous, MvPolynomial.coeff_map]
  exact forall_congr' fun d => imp_congr_left (hf.ne_iff' (map_zero f))

/-- Grading compatibility of `specRingEquiv` with the weighted polynomial grading from which `P_k(w)`
is built (`weightedPolynomialGrading`). -/
theorem specRingEquiv_mem_iff (i : ℕ)
    (a : (Scheme.weightedPolynomialQCAlgebra (Spec (CommRingCat.of k)) w hw).sectionsRing ⊤) :
    a ∈ (Scheme.weightedPolynomialQCAlgebra (Spec (CommRingCat.of k)) w hw).sectionsGrading ⊤ i ↔
      specRingEquiv k w hw a ∈
        MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun i => (⟨w i, hw i⟩ : ℕ+)) i := by
  rw [specRingEquiv_apply, mem_sectionsGrading_iff_isWeightedHomogeneous]
  show _ ↔ _ ∈ MvPolynomial.weightedHomogeneousSubmodule k (fun i => ((⟨w i, hw i⟩ : ℕ+) : ℕ)) i
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact (isWeightedHomogeneous_map_iff w _ (RingEquiv.injective _) _ i).symm

/-- Unit compatibility: the structure map `Γ(Spec k, ⊤) → A` goes to the constants. -/
theorem specRingEquiv_sectionsUnitHom (r : Γ(Spec (CommRingCat.of k), ⊤)) :
    specRingEquiv k w hw
        ((Scheme.weightedPolynomialQCAlgebra (Spec (CommRingCat.of k)) w hw).sectionsUnitHom ⊤ r) =
      MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of k)).hom r) := by
  rw [specRingEquiv_apply, sectionsRingEquiv_sectionsUnitHom, MvPolynomial.map_C]
  rfl

/-- `Proj.map g` followed by the structure map `P_k(w) → Spec k` (which is
`Proj.toSpecZero ≫ Spec.map (algebraMap k _)`, `weightedProjToSpec`), by `proj_map_toSpecZero`. -/
theorem proj_map_weightedProjToSpec {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
    (𝒜 : ℕ → σA) [GradedRing 𝒜] (w' : σ → ℕ+)
    (g : MiyaokaMori.WeightedJets.weightedPolynomialGrading k w' →+*ᵍ 𝒜)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant (MiyaokaMori.WeightedJets.weightedPolynomialGrading k w')).map g) :
    Proj.map g hg ≫ (Proj.toSpecZero (MiyaokaMori.WeightedJets.weightedPolynomialGrading k w') ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (MiyaokaMori.WeightedJets.weightedPolynomialGrading k w' 0)))) =
      Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom
          (algebraMap k (MiyaokaMori.WeightedJets.weightedPolynomialGrading k w' 0)) ≫
        CommRingCat.ofHom g.gradedZeroRingHom) := by
  rw [← Category.assoc, AlgebraicGeometry.Proj.proj_map_toSpecZero, Category.assoc, Spec.map_comp]

/-- The chart structure map of the chart `⊤` of `Spec R`, followed by `⊤.ι`:
`projToOpen ⊤ ≫ ⊤.ι = toSpecZero ≫ Spec.map (sectionsUnit ⊤) ≫ Spec.map (ΓSpecIso R).inv`
(`IsAffineOpen.isoSpec_inv_ι`, `fromSpec_top`, `isoSpec_Spec_inv`; `unitZero ⊤ = sectionsUnit ⊤`
definitionally). Stated for the algebra `T.toGradedAffineAlgebra` of a `GradedQCAlgebra` so that the
grading is `T.sectionsGrading ⊤` (whose `GradedRing` instance is found by instance search). -/
theorem projToOpen_top_comp_ι {R : CommRingCat.{u}} (T : (Spec R).GradedQCAlgebra) :
    T.toGradedAffineAlgebra.projToOpen ⟨⊤, isAffineOpen_top (Spec R)⟩ ≫ (⊤ : (Spec R).Opens).ι =
      Proj.toSpecZero (T.sectionsGrading ⊤) ≫
        Spec.map (CommRingCat.ofHom (T.sectionsUnit ⊤)) ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
  unfold Scheme.GradedAffineAlgebra.projToOpen
  rw [Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv]
  rfl

/-- The degree-zero part of `specRingEquiv⁻¹` sends the constant `c` to the structure map
`sectionsUnit ⊤` applied to `(ΓSpecIso k)⁻¹ c`. -/
theorem gradedZeroRingHom_algebraMap (c : k) :
    (Proj.gradedRingHomOfRingEquivSymm (specRingEquiv k w hw)
        (specRingEquiv_mem_iff k w hw)).gradedZeroRingHom
      (algebraMap k (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun i => (⟨w i, hw i⟩ : ℕ+)) 0) c) =
    (Scheme.weightedPolynomialQCAlgebra (Spec (CommRingCat.of k)) w hw).sectionsUnit ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  apply Subtype.ext
  change (specRingEquiv k w hw).symm (algebraMap k (MvPolynomial σ k) c) =
    (Scheme.weightedPolynomialQCAlgebra (Spec (CommRingCat.of k)) w hw).sectionsUnitHom ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)
  rw [MvPolynomial.algebraMap_eq, RingEquiv.symm_apply_eq, specRingEquiv_sectionsUnitHom]
  congr 1
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

end RelativeProjWeightedPolynomialSpec

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open RelativeProjWeightedPolynomialSpec AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra in
/-- **Affine base case.** Write
`X := Spec k`, `S := weightedPolynomialQCAlgebra X w hw`, `A := S.sectionsRing ⊤` with grading
`S.sectionsGrading ⊤`, `B := MvPolynomial σ k` with grading
`MvPolynomial.weightedHomogeneousSubmodule k w` (this is
`weightedPolynomialGrading k (fun i ↦ ⟨w i, hw i⟩)` by `rfl`, and
`weightedProjectiveSpace k w hw = Proj` of it, `weightedProjTwist k w hw m = Proj.twist _ m` by `rfl`).

Proof:

1. **Proj_X S ≅ Proj A.** `⊤` is an affine open of `Spec k` (`isAffineOpen_top`). The chart square of
   Stacks 01NQ (`GradedAffineAlgebra.projChart_isPullback ⊤`: `Proj A → Proj_X S`, `Proj A → ⊤`, `π`,
   `⊤.ι` is a pullback) has `⊤.ι` an isomorphism (`Scheme.topIso`), so `projChart ⊤` is an isomorphism
   (`pullback.fst` along an isomorphism is an isomorphism). Set `e₀ := (asIso (projChart ⊤)).symm`; by
   `projChart_hom`, `projChart ⊤ ≫ π = projToOpen ⊤ ≫ ⊤.ι` where
   `projToOpen ⊤ = Proj.toSpecZero A ≫ Spec.map (unitZero ⊤) ≫ (isoSpec ⊤).inv`, and
   `(isoSpec ⊤).inv ≫ ⊤.ι = fromSpec = Spec.map (ΓSpecIso k).inv` (`fromSpec_top`, `isoSpec_Spec_inv`).

2. **Graded ring isomorphism `A ≃+* B`.** `specRingEquiv` above: the `j`-th piece of `A` is
   `Γ(⊤, free (weightedMonomials w j))` with the finite index set `weightedMonomials w j`, and
   `sectionsRingEquiv` identifies `Γ(⊤, S) ≃+* Γ(Spec k, ⊤)[x_σ]`
   (degrees and unit preserved); compose with `ΓSpecIso`.

3. **Proj A ≅ P_k(w) over Spec k.** `Proj.isoOfGradedRingEquiv` (Stacks 01MM); its `hom` is
   `Proj.map g` for `g = specRingEquiv⁻¹ : B →+*ᵍ A`, and `proj_map_toSpecZero` gives
   `Proj.map g ≫ toSpecZero B = toSpecZero A ≫ Spec.map g₀`. With `P_k(w) ↘ Spec k = toSpecZero B ≫
   Spec.map (algebraMap k B₀)` the two composites to `Spec k` agree because
   `g (C c) = unitZero ⊤ ((ΓSpecIso k).inv c)` (unit compatibility of step 2). Set `e := e₀ ≪≫ iso`.

4. **Twists.** `twistChartHom m ⊤ : (pullback (projChart ⊤)).obj O(m) ⟶ O_{Proj A}(m)` is an isomorphism
   (`GradedAffineAlgebra.isIso_twistChartHom`, Stacks 01LI), and
   `Proj.twistPullbackHom g m : (pullback (Proj.map g)).obj O_{P(w)}(m) ⟶ O_{Proj A}(m)` is an isomorphism
   (`Proj.isIso_twistPullbackHom_gradedRingHomOfRingEquivSymm`, Stacks 01MX for a graded ring
   isomorphism). Transport along `pullbackId`, `pullbackCongr (e₀.hom ≫ projChart ⊤ = 𝟙)` and `pullbackComp`.

Edge cases: `σ` empty — both sides are the empty scheme (`A = B = k` in degree 0, irrelevant ideal
`0`, `Proj = ∅`) and the statement is trivially true; the theorem does not need `σ` nonempty. -/
theorem relativeProj_weightedPolynomialQCAlgebra_spec_iso (k : Type u) [Field k]
    {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ e : (AlgebraicGeometry.Scheme.relativeProj
      (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
        (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw)).left ≅
      weightedProjectiveSpace k w hw,
      e.hom ≫ (weightedProjectiveSpace k w hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) =
        (AlgebraicGeometry.Scheme.relativeProj
          (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
            (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw)).hom ∧
      ∀ m : ℤ, Nonempty (AlgebraicGeometry.Scheme.relativeProj.twist
          (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
            (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw) m ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (weightedProjTwist k w hw m)) := by
  classical
  set T := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw
    with hT
  -- Step 1: the chart `projChart ⊤` is an isomorphism
  have hpb := (T.toGradedAffineAlgebra.projChart_isPullback
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩).flip
  haveI : IsIso (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of k)).Opens).ι :=
    inferInstanceAs (IsIso (AlgebraicGeometry.Spec (CommRingCat.of k)).topIso.hom)
  have hchart : T.toGradedAffineAlgebra.projChart
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩ =
      hpb.isoPullback.hom ≫ CategoryTheory.Limits.pullback.fst _ _ := hpb.isoPullback_hom_fst.symm
  haveI : IsIso (T.toGradedAffineAlgebra.projChart
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩) := by
    rw [hchart]; infer_instance
  let e₀ : T.toGradedAffineAlgebra.relativeProj.left ≅
      AlgebraicGeometry.Proj (T.sectionsGrading ⊤) :=
    (asIso (T.toGradedAffineAlgebra.projChart
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩)).symm
  have he₀ : e₀.hom ≫ T.toGradedAffineAlgebra.projChart
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩ = 𝟙 _ :=
    IsIso.inv_hom_id (T.toGradedAffineAlgebra.projChart
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩)
  -- Steps 2, 3: the graded ring isomorphism and the Proj isomorphism
  let ι : AlgebraicGeometry.Proj (T.sectionsGrading ⊤) ≅ weightedProjectiveSpace k w hw :=
    AlgebraicGeometry.Proj.isoOfGradedRingEquiv (specRingEquiv k w hw) (specRingEquiv_mem_iff k w hw)
  -- compatibility with the structure maps
  have hι : ι.hom ≫ (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      T.toGradedAffineAlgebra.projChart
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩ ≫
        T.toGradedAffineAlgebra.relativeProj.hom := by
    refine (proj_map_weightedProjToSpec k (T.sectionsGrading ⊤) (fun i => (⟨w i, hw i⟩ : ℕ+))
      (AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm (specRingEquiv k w hw) (specRingEquiv_mem_iff k w hw))
      (AlgebraicGeometry.Proj.irrelevant_le_map_gradedRingHomOfRingEquivSymm _ _)).trans ?_
    refine Eq.trans ?_ (T.toGradedAffineAlgebra.projChart_hom
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩).symm
    refine Eq.trans ?_ (projToOpen_top_comp_ι T).symm
    refine Eq.trans ?_ (congrArg (fun f => AlgebraicGeometry.Proj.toSpecZero (T.sectionsGrading ⊤) ≫ f)
      (AlgebraicGeometry.Spec.map_comp (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv
        (CommRingCat.ofHom (R := Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤))
          (S := CommRingCat.of (T.sectionsGrading ⊤ 0)) (T.sectionsUnit ⊤))))
    refine congrArg (fun f => AlgebraicGeometry.Proj.toSpecZero (T.sectionsGrading ⊤) ≫
      AlgebraicGeometry.Spec.map f) ?_
    ext c
    exact congrArg Subtype.val (gradedZeroRingHom_algebraMap k w hw c)
  refine ⟨e₀ ≪≫ ι, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (fun f => e₀.hom ≫ f) hι).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ T.toGradedAffineAlgebra.relativeProj.hom) he₀).trans
          (Category.id_comp _))))
  · intro m
    have i1 := T.toGradedAffineAlgebra.isIso_twistChartHom m
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    have i2 := AlgebraicGeometry.Proj.isIso_twistPullbackHom_gradedRingHomOfRingEquivSymm
      (specRingEquiv k w hw) (specRingEquiv_mem_iff k w hw) m
    refine ⟨((AlgebraicGeometry.Scheme.Modules.pullbackId _).app _).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr he₀.symm).app _ ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp e₀.hom
        (T.toGradedAffineAlgebra.projChart
          ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩)).app _).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback e₀.hom).mapIso
        (@asIso _ _ _ _ (T.toGradedAffineAlgebra.twistChartHom m
          ⟨⊤, AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (CommRingCat.of k))⟩) i1 ≪≫
          (@asIso _ _ _ _ (AlgebraicGeometry.Proj.twistPullbackHom
            (AlgebraicGeometry.Proj.gradedRingHomOfRingEquivSymm (specRingEquiv k w hw) (specRingEquiv_mem_iff k w hw))
            (AlgebraicGeometry.Proj.irrelevant_le_map_gradedRingHomOfRingEquivSymm _ _) m) i2).symm) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e₀.hom ι.hom).app _⟩

end
