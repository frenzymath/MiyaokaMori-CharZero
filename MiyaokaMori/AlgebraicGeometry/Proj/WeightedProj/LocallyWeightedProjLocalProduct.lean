import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01n2
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01nr
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLocalIso

/-! # Local product structure of the relative Proj of a locally weighted polynomial algebra

The relative Proj of a locally weighted polynomial graded algebra is locally a product: there is an
open cover of the base such that over each piece `U_i`, `Proj S ≅ U_i ×_k P_k(w)` compatibly with
the projections, and `O(m)` corresponds to `pr_2^* O(m)`. This is the statement "locally over `C`,
`Y_k^GG` is a product with the weighted projective space" used in the proof of the Veronese
polarization lemma of the paper.

## Route

The hypothesis `hS` is an atlas `𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w`: affine
opens `U_i = 𝒜.chart i` covering `X` with graded ring isomorphisms `S(U_i) ≃+* Γ(X,U_i)[x]_w`. The
cover of the statement is the atlas cover (`openCoverULift`), and on each chart the isomorphism is
the composite of three squares:

* **(A)** `Proj S(U_i) ≅ π⁻¹(U_i)`: the chart square of the glued relative Proj is a pullback
  (`GradedAffineAlgebra.projChart_isPullback`, Stacks 01NQ);
* **(B)** `Proj S(U_i) ≅ Proj Γ(X,U_i)[x]_w`: `Proj.map` of the atlas isomorphism (`projIso`),
  compatible with the structure maps to `U_i` (`projIso_hom_weightedProjToOpen`);
* **(C)** `Proj Γ(X,U_i)[x]_w ≅ U_i ×_k P_k(w)`: Proj commutes with the base change
  `k → Γ(X,U_i)` (Stacks 01N2, `Proj.isPullback_of_isBaseChange`), where
  `Γ(X,U_i)[x]_w = Γ(X,U_i) ⊗_k k[x]_w` is Mathlib's `MvPolynomial.algebraTensorAlgEquiv`
  (`weightedProj_baseChange_isPullback`).

`O(m)` is transported along the same three squares: (A) `twistChartHom` is an isomorphism
(`isIso_twistChartHom`, derived from Stacks 01NR's `isIso_twistAffineHom`), (B) θ along a graded ring
isomorphism is an isomorphism (`Proj.isIso_twistPullbackHom_of_bijective`, proved in this file),
(C) θ along the base change is an isomorphism (Stacks 01N2, `Proj.isIso_twistPullbackHom`).

`Proj.isIso_twistPullbackHom_of_bijective` is proved by reduction to
`isIso_twistPullbackHom_of_isLocalizationAway` with `f = 1`.

**Universe of the cover.** `X.OpenCover` carries a universe parameter for the index type; the
statement `∃ 𝒰 : X.OpenCover.{u_1}, …` is not provable for `u_1 < u` (there need not be a
`Type u_1`-indexed trivializing cover), so the statement reads `X.OpenCover.{max u v}` (the atlas
index `ULift`-ed).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

variable {X : AlgebraicGeometry.Scheme.{u}} {S : X.GradedAffineAlgebra}
variable {σ : Type u} {w : σ → ℕ}

noncomputable def openCover (𝒜 : S.WeightedPolynomialAtlas w) : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun i => (𝒜.chart i).toOpens) (by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [eq_top_iff]
    intro x hx
    obtain ⟨i, hi⟩ := 𝒜.exists_chart_mem x
    exact Opens.mem_iSup.mpr ⟨i, hi⟩)

@[simp] theorem openCover_f (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    (𝒜.openCover).f i = (𝒜.chart i).toOpens.ι := rfl

/-- The atlas cover with its index type lifted to `Type (max u v)` (the statement of
`relativeProj_locallyWeighted_localProduct` is universe polymorphic in the index universe). -/
noncomputable def openCoverULift (𝒜 : S.WeightedPolynomialAtlas w) : X.OpenCover.{max u v} :=
  X.openCoverOfIsOpenCover (fun i : ULift.{v} 𝒜.I => (𝒜.chart i.down).toOpens) (by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [eq_top_iff]
    intro x hx
    obtain ⟨i, hi⟩ := 𝒜.exists_chart_mem x
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩)

@[simp] theorem openCoverULift_f (𝒜 : S.WeightedPolynomialAtlas w) (i : ULift.{v} 𝒜.I) :
    (openCoverULift.{u, v} 𝒜).f i = (𝒜.chart i.down).toOpens.ι := rfl

end AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
variable [GradedRing 𝒜] [GradedRing ℬ]

/-- A degree-preserving ring equivalence induces an isomorphism of Proj schemes.

The orientation follows `Proj.map`: a ring map `A → B` gives a scheme map
`Proj B ⟶ Proj A`.  The two irrelevant-ideal hypotheses are derived from the
degreewise equivalence, so callers only need to provide preservation of graded
pieces in both directions.
-/
noncomputable def isoOfRingEquiv (e : A ≃+* B)
    (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) : Proj 𝒜 ≅ Proj ℬ := by
  let f : 𝒜 →+*ᵍ ℬ :=
    { toRingHom := e.toRingHom
      map_mem := fun {i} {a} ha => (he i a).mp ha }
  let g : ℬ →+*ᵍ 𝒜 :=
    { toRingHom := e.symm.toRingHom
      map_mem := fun {i} {b} hb => (he i (e.symm b)).mpr (by simpa using hb) }
  have hf : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f := by
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi b hb
    change b ∈ ℬ i at hb
    rw [← show f (e.symm b) = b by simp [f]]
    apply Ideal.mem_map_of_mem f.toRingHom
    exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi
      ((he i (e.symm b)).mpr (by simpa using hb))
  have hg : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant ℬ).map g := by
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi a ha
    change a ∈ 𝒜 i at ha
    rw [← show g (e a) = a by simp [g]]
    apply Ideal.mem_map_of_mem g.toRingHom
    exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi
      ((he i a).mp ha)
  refine
    { hom := Proj.map g hg
      inv := Proj.map f hf
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← Proj.map_comp f g hf hg]
    have hfg : g.comp f = GradedRingHom.id 𝒜 := by
      ext a
      simp [f, g]
    have hmap : Proj.map (g.comp f)
        (HomogeneousIdeal.irrelevant_le_map_comp hf hg) =
        Proj.map (GradedRingHom.id 𝒜) (by simp) := by
      congr 1
    exact hmap.trans Proj.map_id
  · rw [← Proj.map_comp g f hg hf]
    have hgf : f.comp g = GradedRingHom.id ℬ := by
      ext b
      simp [f, g]
    have hmap : Proj.map (f.comp g)
        (HomogeneousIdeal.irrelevant_le_map_comp hg hf) =
        Proj.map (GradedRingHom.id ℬ) (by simp) := by
      congr 1
    exact hmap.trans Proj.map_id

end AlgebraicGeometry.Proj

namespace MvPolynomial

variable {σ : Type u} {R R' : Type u} [CommRing R] [CommRing R'] (w : σ → ℕ)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- `MvPolynomial.map φ` preserves weighted homogeneity (coefficients are mapped by `φ`,
so the support can only shrink). -/
theorem IsWeightedHomogeneous.map_ringHom (φ : R →+* R') {p : MvPolynomial σ R} {m : ℕ}
    (hp : p.IsWeightedHomogeneous w m) :
    (MvPolynomial.map φ p).IsWeightedHomogeneous w m := by
  intro d hd
  apply hp
  intro h
  apply hd
  rw [MvPolynomial.coeff_map, h, map_zero]

/-- Base change of the weighted polynomial ring along `φ : R →+* R'`, as a graded ring
homomorphism `R[x]_w →+*ᵍ R'[x]_w`. -/
def weightedMapGraded (φ : R →+* R') :
    MvPolynomial.weightedHomogeneousSubmodule R w →+*ᵍ
      MvPolynomial.weightedHomogeneousSubmodule R' w where
  toRingHom := MvPolynomial.map φ
  map_mem := fun {m} {p} hp =>
    (MvPolynomial.mem_weightedHomogeneousSubmodule R' w m _).mpr
      (((MvPolynomial.mem_weightedHomogeneousSubmodule R w m p).mp hp).map_ringHom w φ)

@[simp] theorem weightedMapGraded_apply (φ : R →+* R') (p : MvPolynomial σ R) :
    weightedMapGraded w φ p = MvPolynomial.map φ p := rfl

/-- The base change map satisfies the `Proj.map` hypothesis: every positive-degree weighted
homogeneous polynomial over `R'` is an `R'`-combination of monomials, which come from `R`. -/
theorem weightedMapGraded_irrelevant_le (φ : R →+* R') :
    HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule R' w) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule R w)).map
        (weightedMapGraded w φ) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro m hm p hp
  have hp' : p.IsWeightedHomogeneous w m := hp
  show p ∈ Ideal.map (weightedMapGraded w φ).toRingHom
    (HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule R w)).toIdeal
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hmono : MvPolynomial.monomial d (MvPolynomial.coeff d p) =
      MvPolynomial.C (MvPolynomial.coeff d p) *
        (weightedMapGraded w φ).toRingHom (MvPolynomial.monomial d (1 : R)) := by
    change _ = _ * MvPolynomial.map φ (MvPolynomial.monomial d 1)
    rw [MvPolynomial.map_monomial, map_one, MvPolynomial.C_mul_monomial, mul_one]
  rw [hmono]
  refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
  refine HomogeneousIdeal.mem_irrelevant_of_mem _ hm ?_
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact MvPolynomial.isWeightedHomogeneous_monomial w d 1 (hp' (MvPolynomial.mem_support_iff.mp hd))

end MvPolynomial

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

variable {X : AlgebraicGeometry.Scheme.{u}} {S : X.GradedAffineAlgebra}
variable {σ : Type u} {w : σ → ℕ}
attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The inverse atlas equivalence `Γ(X,U_i)[x]_w → S(U_i)` as a graded ring homomorphism. -/
def gradedSymm (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w →+*ᵍ
      S.grading (𝒜.chart i) where
  toRingHom := (𝒜.equiv i).symm.toRingHom
  map_mem := fun {m} {b} hb => (𝒜.equiv_grading i m _).mpr (by simpa using hb)

@[simp] theorem gradedSymm_apply (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I)
    (p : MvPolynomial σ Γ(X, (𝒜.chart i).toOpens)) :
    𝒜.gradedSymm i p = (𝒜.equiv i).symm p := rfl

/-- `gradedSymm` satisfies the `Proj.map` hypothesis (it is an isomorphism). -/
theorem gradedSymm_irrelevant_le (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    HomogeneousIdeal.irrelevant (S.grading (𝒜.chart i)) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w)).map
        (𝒜.gradedSymm i) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro m hm a ha
  rw [← show 𝒜.gradedSymm i ((𝒜.equiv i) a) = a by simp]
  apply Ideal.mem_map_of_mem (𝒜.gradedSymm i).toRingHom
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ hm
    ((𝒜.equiv_grading i m a).mp ha)

/-- Every chart of a weighted-polynomial atlas identifies its local Proj with
the Proj of the corresponding weighted polynomial ring. -/
noncomputable def projIso (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    AlgebraicGeometry.Proj (S.grading (𝒜.chart i)) ≅
      AlgebraicGeometry.Proj
        (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w) :=
  AlgebraicGeometry.Proj.isoOfRingEquiv (𝒜.equiv i) fun m a => by
    simpa only [MvPolynomial.mem_weightedHomogeneousSubmodule] using
      𝒜.equiv_grading i m a

/-- The forward map of `projIso` is `Proj.map` of the inverse atlas equivalence. -/
theorem projIso_hom (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    (𝒜.projIso i).hom =
      AlgebraicGeometry.Proj.map (𝒜.gradedSymm i) (𝒜.gradedSymm_irrelevant_le i) := rfl

/-- The atlas Proj isomorphism is compatible with the canonical degree-zero
structure maps. -/
theorem projIso_hom_toSpecZero (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    (𝒜.projIso i).hom ≫
        AlgebraicGeometry.Proj.toSpecZero
          (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w) =
      AlgebraicGeometry.Proj.toSpecZero (S.grading (𝒜.chart i)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (𝒜.gradedSymm i).gradedZeroRingHom) := by
  rw [projIso_hom]
  exact AlgebraicGeometry.Proj.proj_map_toSpecZero _ _

/-- The structure morphism `Proj Γ(X,U_i)[x]_w ⟶ U_i` of the local weighted model
(through the degree-zero part and `U_i ≅ Spec Γ(X,U_i)`). -/
def weightedProjToOpen (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    AlgebraicGeometry.Proj
        (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w) ⟶
      (𝒜.chart i).toOpens.toScheme :=
  AlgebraicGeometry.Proj.toSpecZero _ ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Γ(X, (𝒜.chart i).toOpens)
      (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w 0))) ≫
    (𝒜.chart i).2.isoSpec.inv

/-- Degree-zero compatibility of the atlas: `gradedSymm` sends the constant `C r` to the
structure map `unitZero r` (from `equiv_unit`). -/
theorem gradedZeroRingHom_comp_algebraMap (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    (𝒜.gradedSymm i).gradedZeroRingHom.comp (algebraMap Γ(X, (𝒜.chart i).toOpens)
      (MvPolynomial.weightedHomogeneousSubmodule Γ(X, (𝒜.chart i).toOpens) w 0)) =
      S.unitZero (𝒜.chart i) := by
  ext r
  change (𝒜.equiv i).symm (algebraMap Γ(X, (𝒜.chart i).toOpens)
      (MvPolynomial σ Γ(X, (𝒜.chart i).toOpens)) r) = S.toAffineAlgebra.unitHom (𝒜.chart i) r
  rw [MvPolynomial.algebraMap_eq, RingEquiv.symm_apply_eq, 𝒜.equiv_unit]

/-- The atlas Proj isomorphism is compatible with the structure morphisms to the chart. -/
theorem projIso_hom_weightedProjToOpen (𝒜 : S.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    (𝒜.projIso i).hom ≫ 𝒜.weightedProjToOpen i = S.projToOpen (𝒜.chart i) := by
  unfold weightedProjToOpen AlgebraicGeometry.Scheme.GradedAffineAlgebra.projToOpen
  rw [← Category.assoc, projIso_hom_toSpecZero, Category.assoc, ← Category.assoc (Spec.map _),
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, gradedZeroRingHom_comp_algebraMap]

end AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas

namespace AlgebraicGeometry.Scheme.AffineZariskiSite

variable {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}

/-- The ring map `k → Γ(X,U)` corresponding to `U ≅ Spec Γ(X,U) → X → Spec k`
(`Spec` is fully faithful). -/
def baseRingHom (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (U : X.AffineZariskiSite) :
    CommRingCat.of k ⟶ Γ(X, U.toOpens) :=
  AlgebraicGeometry.Spec.preimage (U.2.isoSpec.inv ≫ U.toOpens.ι ≫ pX)

@[simp] theorem Spec_map_baseRingHom (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (U : X.AffineZariskiSite) :
    AlgebraicGeometry.Spec.map (baseRingHom pX U) = U.2.isoSpec.inv ≫ U.toOpens.ι ≫ pX :=
  AlgebraicGeometry.Spec.map_preimage _

theorem isoSpec_hom_Spec_map_baseRingHom (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (U : X.AffineZariskiSite) :
    U.2.isoSpec.hom ≫ AlgebraicGeometry.Spec.map (baseRingHom pX U) = U.toOpens.ι ≫ pX := by
  rw [Spec_map_baseRingHom, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme.AffineZariskiSite

section WeightedBaseChange

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- `Proj` of the weighted polynomial ring commutes with base change along `ψ : k → R`
(Stacks 01N2, applied to `R[x]_w = R ⊗_k k[x]_w`): the square
`Proj R[x]_w → P_k(w)`, `Proj R[x]_w → Spec R`, `P_k(w) → Spec k`, `Spec R → Spec k` is a pullback.
The base change hypothesis is `MvPolynomial.algebraTensorAlgEquiv`. -/
theorem weightedProj_baseChange_isPullback (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (R : CommRingCat.{u}) (ψ : CommRingCat.of k ⟶ R) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.Proj.map (MvPolynomial.weightedMapGraded w ψ.hom)
        (MvPolynomial.weightedMapGraded_irrelevant_le w ψ.hom))
      (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.weightedHomogeneousSubmodule R w) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap R (MvPolynomial.weightedHomogeneousSubmodule R w 0))))
      (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (AlgebraicGeometry.Spec.map ψ) := by
  let _ : Algebra k R := ψ.hom.toAlgebra
  have hbc : IsBaseChange R (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k R)).toLinearMap :=
    IsBaseChange.of_equiv (MvPolynomial.algebraTensorAlgEquiv k R).toLinearEquiv fun p => by
      simp only [AlgEquiv.toLinearEquiv_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul,
        AlgHom.toLinearMap_apply, MvPolynomial.mapAlgHom_apply]
      rfl
  have h := AlgebraicGeometry.Proj.isPullback_of_isBaseChange
    (MvPolynomial.weightedHomogeneousSubmodule k w)
    (MvPolynomial.weightedHomogeneousSubmodule R w)
    (MvPolynomial.weightedMapGraded w ψ.hom) (MvPolynomial.weightedMapGraded_irrelevant_le w ψ.hom)
    (MvPolynomial.mapAlgHom (Algebra.ofId k R)) (fun a => rfl) hbc
  exact h

/-- The twist comparison θ of Stacks 01MX along the base change `Proj R[x]_w → P_k(w)` is an
isomorphism (Stacks 01N2, `Proj.isIso_twistPullbackHom` with the base change data of
`weightedProj_baseChange_isPullback`). -/
theorem weightedProj_baseChange_isIso_twistPullbackHom (k : Type u) [Field k] {σ : Type u}
    [Fintype σ] (w : σ → ℕ) (R : CommRingCat.{u}) (ψ : CommRingCat.of k ⟶ R) (m : ℤ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom
      (MvPolynomial.weightedMapGraded w ψ.hom)
      (MvPolynomial.weightedMapGraded_irrelevant_le w ψ.hom) m) := by
  let _ : Algebra k R := ψ.hom.toAlgebra
  have hbc : IsBaseChange R (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k R)).toLinearMap :=
    IsBaseChange.of_equiv (MvPolynomial.algebraTensorAlgEquiv k R).toLinearEquiv fun p => by
      simp only [AlgEquiv.toLinearEquiv_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul,
        AlgHom.toLinearMap_apply, MvPolynomial.mapAlgHom_apply]
      rfl
  exact AlgebraicGeometry.Proj.isIso_twistPullbackHom
    (MvPolynomial.weightedHomogeneousSubmodule k w)
    (MvPolynomial.weightedHomogeneousSubmodule R w)
    (MvPolynomial.weightedMapGraded w ψ.hom) (MvPolynomial.weightedMapGraded_irrelevant_le w ψ.hom)
    (MvPolynomial.mapAlgHom (Algebra.ofId k R)) (fun a => rfl) hbc m

end WeightedBaseChange

/-- **Stacks 01MX, θ for a graded ring isomorphism.**

If the graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` is bijective, then the comparison
morphism `θ = Proj.twistPullbackHom f hf n : (Proj.map f hf)^* O_{Proj 𝒜}(n) ⟶ O_{Proj ℬ}(n)`
is an isomorphism.

Proof. A bijective `f` is the special case `B = A[1/1]` of the
degree-0 localization theorem `isIso_twistPullbackHom_of_isLocalizationAway`
(Stacks 01MX for `B = A[1/f]`, `f ∈ 𝒜 0`), whose three hypotheses are:
1. `1 ∈ 𝒜 0` (`SetLike.one_mem_graded`);
2. `IsLocalization.Away (1 : A) B` along `f`: a bijective ring map is the localization at the unit `1`
   (Mathlib `IsLocalization.away_of_isUnit_of_bijective`);
3. `Proj.map f hf` is an open immersion. It is even an isomorphism: the inverse `f⁻¹` is again graded —
   for `f a ∈ ℬ i` and `j ≠ i`, `f (decompose 𝒜 a)_j = (decompose ℬ (f a))_j = 0`
   (`GradedRingHom.map_directSumDecompose`, `DirectSum.decompose_of_mem_ne`), so `(decompose 𝒜 a)_j = 0`
   by injectivity and `a = ∑_j (decompose 𝒜 a)_j = (decompose 𝒜 a)_i ∈ 𝒜 i` — hence
   `RingEquiv.ofBijective f` satisfies the hypothesis of `Proj.isoOfRingEquiv`, and `Proj.map f hf` is
   the `inv` of that isomorphism (`GradedRingHom.ext`). Open immersion: `IsOpenImmersion.of_isIso`.

Source: Stacks 01MX (`lemma-morphism-proj`, functoriality of θ), Stacks 01MM. Used by
`relativeProj_locallyWeighted_chart` (this file) to transport `O(m)` along the atlas isomorphism
`Proj S(U_i) ≅ Proj Γ(X,U_i)[x]_w`.

Edge cases: `𝒜 = ℬ`, `f = id` gives `θ = id` (`Proj.map_id`); the zero ring gives `Proj = ∅` and the
statement is vacuous. -/
theorem AlgebraicGeometry.Proj.isIso_twistPullbackHom_of_bijective {σ τ A B : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hbij : Function.Bijective f) (n : ℤ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom f hf n) := by
  classical
  -- Step 1: the inverse of `f` is graded, i.e. `f a ∈ ℬ i → a ∈ 𝒜 i`.
  have hback : ∀ (i : ℕ) (a : A), f a ∈ ℬ i → a ∈ 𝒜 i := by
    intro i a ha
    have hzero : ∀ j, j ≠ i → (DirectSum.decompose 𝒜 a j : A) = 0 := by
      intro j hj
      apply hbij.injective
      rw [GradedRingHom.map_directSumDecompose, map_zero,
        DirectSum.decompose_of_mem_ne ℬ ha (Ne.symm hj)]
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine sum_mem fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      exact (DirectSum.decompose 𝒜 a j).2
    · rw [hzero j hj]
      exact zero_mem _
  -- Step 2: `Proj.map f hf` is an isomorphism (inverse of `Proj.isoOfRingEquiv`), hence an open
  -- immersion.
  let e : A ≃+* B := RingEquiv.ofBijective (f : A →+* B) hbij
  have he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i := fun i a =>
    ⟨fun h => f.map_mem h, hback i a⟩
  have hmap : AlgebraicGeometry.Proj.map f hf = (AlgebraicGeometry.Proj.isoOfRingEquiv e he).inv := by
    show AlgebraicGeometry.Proj.map f hf = AlgebraicGeometry.Proj.map _ _
    congr 1
  have : CategoryTheory.IsIso (AlgebraicGeometry.Proj.map f hf) := by
    rw [hmap]; infer_instance
  have : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Proj.map f hf) :=
    AlgebraicGeometry.IsOpenImmersion.of_isIso _
  -- Step 3: `B = A[1/1]` via the bijective `f`; apply the degree-0 localization case.
  have hloc : letI := f.toRingHom.toAlgebra; IsLocalization.Away (1 : A) B := by
    let _ := f.toRingHom.toAlgebra
    exact IsLocalization.away_of_isUnit_of_bijective B isUnit_one hbij
  exact MiyaokaMori.RelativeProjTwistLocalIso.isIso_twistPullbackHom_of_isLocalizationAway f hf
    (SetLike.one_mem_graded 𝒜) hloc n

/-- Pullback of sheaves of modules along an isomorphism of schemes reflects isomorphisms
(`pullback e.hom ⋙ pullback e.inv ≅ 𝟭`). -/
theorem AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_map
    {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) {M N : Y.Modules} (φ : M ⟶ N)
    [CategoryTheory.IsIso ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).map φ)] :
    CategoryTheory.IsIso φ := by
  have h : CategoryTheory.IsIso ((AlgebraicGeometry.Scheme.Modules.pullback e.hom ⋙
      AlgebraicGeometry.Scheme.Modules.pullback e.inv).map φ) := by
    change CategoryTheory.IsIso ((AlgebraicGeometry.Scheme.Modules.pullback e.inv).map
      ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).map φ))
    infer_instance
  let α : AlgebraicGeometry.Scheme.Modules.pullback e.hom ⋙
      AlgebraicGeometry.Scheme.Modules.pullback e.inv ≅ 𝟭 _ :=
    AlgebraicGeometry.Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackId Y
  exact (NatIso.isIso_map_iff α φ).mp h

/-- **Stacks 01LI for the twisting sheaf**: restricted to the chart `Proj S(U) ↪ Proj_X S`, the glued
sheaf `O_{Proj_X S}(m)` is `O_{Proj S(U)}(m)`, i.e. `twistChartHom` is an isomorphism.
Derived from `relativeProj.isIso_twistAffineHom` (Stacks 01NR): `twistAffineHom` is
`(three isomorphisms) ≫ (pullback e.hom).map (twistChartHom m U)` with `e = affineIso S U`, and
pullback along the isomorphism `e` reflects isomorphisms. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.isIso_twistChartHom
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℤ)
    (U : X.affineOpens) :
    CategoryTheory.IsIso (S.toGradedAffineAlgebra.twistChartHom m ⟨U.1, U.2⟩) := by
  have h := AlgebraicGeometry.Scheme.relativeProj.isIso_twistAffineHom S U m
  unfold AlgebraicGeometry.Scheme.relativeProj.twistAffineHom at h
  dsimp only at h
  have h2 := @CategoryTheory.IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h
  have h3 := @CategoryTheory.IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h2
  have h4 := @CategoryTheory.IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h3
  exact @AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_map _ _
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U) _ _ _ h4

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- **One chart of the local product.** For a chart `U_i` of the atlas, `π⁻¹(U_i) ≅ U_i ×_k P_k(w)`
compatibly with the projections to `U_i`, and `O(m)` corresponds to `pr_2^* O_{P(w)}(m)`.
Composite of the three squares (A), (B), (C) described in the module docstring. -/
theorem relativeProj_locallyWeighted_chart {k : Type u}
    [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (S : X.GradedQCAlgebra) {σ : Type u} [Fintype σ] (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (𝒜 : S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) (i : 𝒜.I) :
    ∃ φ : CategoryTheory.Limits.pullback
          (AlgebraicGeometry.Scheme.relativeProj S).hom ((𝒜.chart i).toOpens.ι) ≅
        CategoryTheory.Limits.pullback ((𝒜.chart i).toOpens.ι ≫ pX)
          (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)),
      φ.hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
          CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.relativeProj S).hom
            ((𝒜.chart i).toOpens.ι) ∧
        ∀ m : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
            (CategoryTheory.Limits.pullback.fst
              (AlgebraicGeometry.Scheme.relativeProj S).hom ((𝒜.chart i).toOpens.ι))).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist S m) ≅
          (AlgebraicGeometry.Scheme.Modules.pullback
            (φ.hom ≫ CategoryTheory.Limits.pullback.snd _ _)).obj
            (weightedProjTwist k w hw m)) := by
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
  -- (B) the atlas identifies the chart's Proj with the weighted polynomial Proj
  refine ⟨eA.symm ≪≫ 𝒜.projIso i ≪≫ eC, ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc, hC1,
      AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas.projIso_hom_weightedProjToOpen,
      Iso.inv_comp_eq, hA2]
  · intro m
    have hfst : CategoryTheory.Limits.pullback.fst (AlgebraicGeometry.Scheme.relativeProj S).hom
        (𝒜.chart i).toOpens.ι = eA.inv ≫ S.toGradedAffineAlgebra.projChart (𝒜.chart i) :=
      (Iso.eq_inv_comp eA).mpr hA1
    have hsnd : (eA.symm ≪≫ 𝒜.projIso i ≪≫ eC).hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
        eA.inv ≫ ((𝒜.projIso i).hom ≫
          AlgebraicGeometry.Proj.map (MvPolynomial.weightedMapGraded w
              (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom)
            (MvPolynomial.weightedMapGraded_irrelevant_le w
              (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom)) := by
      rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc, hC2]
      rfl
    have i1 : CategoryTheory.IsIso (S.toGradedAffineAlgebra.twistChartHom m (𝒜.chart i)) :=
      AlgebraicGeometry.Scheme.GradedQCAlgebra.isIso_twistChartHom S m ⟨(𝒜.chart i).1, (𝒜.chart i).2⟩
    have i2 := weightedProj_baseChange_isIso_twistPullbackHom k w Γ(X, (𝒜.chart i).toOpens)
      (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)) m
    have i3 := AlgebraicGeometry.Proj.isIso_twistPullbackHom_of_bijective (𝒜.gradedSymm i)
      (𝒜.gradedSymm_irrelevant_le i) (𝒜.equiv i).symm.bijective m
    refine ⟨(AlgebraicGeometry.Scheme.Modules.pullbackCongr hfst).app _ ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp eA.inv _).app _).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback eA.inv).mapIso
        (@asIso _ _ _ _ (S.toGradedAffineAlgebra.twistChartHom m (𝒜.chart i)) i1) ≪≫ ?_ ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hsnd).app _).symm⟩
    refine ?_ ≪≫ (AlgebraicGeometry.Scheme.Modules.pullbackComp eA.inv _).app _
    refine (AlgebraicGeometry.Scheme.Modules.pullback eA.inv).mapIso ?_
    refine ?_ ≪≫ (AlgebraicGeometry.Scheme.Modules.pullbackComp (𝒜.projIso i).hom _).app _
    refine ?_ ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback (𝒜.projIso i).hom).mapIso
      (@asIso _ _ _ _ (AlgebraicGeometry.Proj.twistPullbackHom (MvPolynomial.weightedMapGraded w
          (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom)
        (MvPolynomial.weightedMapGraded_irrelevant_le w
          (AlgebraicGeometry.Scheme.AffineZariskiSite.baseRingHom pX (𝒜.chart i)).hom) m) i2).symm
    exact (@asIso _ _ _ _ (AlgebraicGeometry.Proj.twistPullbackHom (𝒜.gradedSymm i)
      (𝒜.gradedSymm_irrelevant_le i) m) i3).symm

/-- **Local product structure of the relative Proj of a locally weighted polynomial algebra.**
The cover is the atlas cover of `hS` (index type lifted to `Type (max u v)`, see the module
docstring), and each chart is `relativeProj_locallyWeighted_chart`. -/
theorem relativeProj_locallyWeighted_localProduct {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (S : X.GradedQCAlgebra) {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) :
    ∃ 𝒰 : X.OpenCover.{max u v}, ∀ i, ∃ φ : CategoryTheory.Limits.pullback
          (AlgebraicGeometry.Scheme.relativeProj S).hom (𝒰.f i) ≅
        CategoryTheory.Limits.pullback (𝒰.f i ≫ pX)
          (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)),
      φ.hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
          CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.relativeProj S).hom (𝒰.f i) ∧
        ∀ m : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst
            (AlgebraicGeometry.Scheme.relativeProj S).hom (𝒰.f i))).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist S m) ≅
          (AlgebraicGeometry.Scheme.Modules.pullback
            (φ.hom ≫ CategoryTheory.Limits.pullback.snd _ _)).obj (weightedProjTwist k w hw m)) := by
  obtain ⟨𝒜⟩ := hS
  exact ⟨AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas.openCoverULift.{u, v} 𝒜,
    fun i => relativeProj_locallyWeighted_chart pX S w hw 𝒜 (ULift.down i)⟩

end
