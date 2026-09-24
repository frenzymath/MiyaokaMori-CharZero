import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.LaurentCechCohomology
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingElementwise
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverTwist
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mnTwistSectionBijective
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationScalar

/-! # The Čech terms of `O(d)` on projective space are Laurent–Čech terms

Let `R` be a commutative ring, `X = P^N_R`, `U_i = D_+(T_i)`, `M = O(d)`. There is a family of additive
isomorphisms `e_σ : Γ(O(d), U_{σ_0} ∩ ⋯ ∩ U_{σ_p}) ≃ (R[T]_{T_{σ_0}⋯T_{σ_p}})_d` (`σ` strictly
increasing), compatible with restriction maps and `R`-linear. Consequently, under `e` the differential
`cechFamilyD` on families of sections is the Laurent–Čech differential `LaurentCech.δ`, and the vanishing
of the homology of the alternating Čech complex `cechComplexAlt` follows from that of the Laurent–Čech
complex.

Proof sketch:
1. `⋂_j D_+(T_{σ j}) = D_+(T_σ)` (`iInf_chart_eq`: a prime ideal contains a product iff it contains a
   factor, `Ideal.IsPrime.prod_mem_iff`).
2. `(R[T]_{T_σ})_d` (`LaurentCech.degPiece`) is the `twistAway` submodule of Stacks 01N2
   (`degPiece_eq_twistAway`, same generating set).
3. Stacks 01MN: `twistSection : (S_{T_σ})_d → Γ(D_+(T_σ), O(d))`, `a/T_σ^j ↦ (z ↦ a/T_σ^j ∈ S_z)`, is
   bijective (`MiyaokaMori.Stacks01mn.twistSection_bijective`: `T_{σ 0}` is a degree-one factor of `T_σ`, so
   `T_{σ 0}^{±d}` is a frame of `O(d)` on `D_+(T_σ)` (`homogeneousFrameSectionEquiv` /
   `inverseFrameSectionEquiv`), together with Mathlib's `Proj.basicOpenIsoAway` (`Γ(D_+(f), O) = S_(f)`)).
   `e_σ` is its inverse (`termEquiv`).
4. Compatibility with restriction and `R`-linearity hold pointwise: at `z` both sides are the image of
   the same fraction in `S_z` (`toFiber_map_eq`, `toFiber_smul`; the pointwise value `r/1` of the scalar
   `scalar r` is `Proj.zeroToGlobal_apply_val`, `scalar_apply_val`).

Source: the first paragraph of the proof of Stacks 01XT; 01MN (`Γ(D_+(f), O(d)) = (S_f)_d`), 01MK.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace ProjectiveSpaceOver

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

/-- The scalars `R → Γ(P^N_R, V)`: `R ≅ Γ(Spec R, ⊤) → Γ(P^N_R, ⊤) → Γ(P^N_R, V)`. The same
`R → Γ(X, ⊤)` as used by `sheafCohomology.moduleOver`. -/
def scalar (N : ℕ) (R : Type u) [CommRing R] (V : (ProjectiveSpaceOver N R).Opens) :
    R →+* Γ(ProjectiveSpaceOver N R, V) :=
  ((ProjectiveSpaceOver N R).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ProjectiveSpaceOver.toSpecBase N R).appTop).hom


/-! ## The charts `⋂_j D_+(T_{σ j}) = D_+(T_σ)` and the terms `(R[T]_{T_σ})_d = twistAway` -/

attribute [local instance] MvPolynomial.gradedAlgebra

section Terms

open LaurentCech MiyaokaMori.Stacks01mn MiyaokaMori.Stacks01n2 MiyaokaMori.Stacks01n2TwistStalk

variable (R : Type u) [CommRing R] (N : ℕ)

theorem prodX_mem (S : Finset (Fin (N + 1))) :
    prodX R N S ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R S.card :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (prodX_isHomogeneous S)

theorem card_pos (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    0 < (Finset.univ.map σ.toEmbedding).card := by
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  exact Nat.succ_pos p

/-- For the standard cover: `⋂_j D_+(T_{σ j}) = D_+(T_σ)`, `T_σ = ∏_j T_{σ j}` (a prime ideal contains a
product iff it contains a factor). -/
theorem iInf_chart_eq (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    (⨅ j, chart N R (σ j)) = AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (prodX R N (Finset.univ.map σ.toEmbedding)) := by
  ext x
  have hp := x.isPrime
  rw [Opens.coe_iInf, Set.mem_iInter]
  simp only [SetLike.mem_coe, chart, prodX, Finset.prod_map, RelEmbedding.coe_toEmbedding]
  change (∀ i, MvPolynomial.X (σ i) ∉ x.asHomogeneousIdeal.toIdeal) ↔
    ∏ i, MvPolynomial.X (σ i) ∉ x.asHomogeneousIdeal.toIdeal
  rw [Ideal.IsPrime.prod_mem_iff]
  simp

/-- `(R[T]_{T_S})_d` (`degPiece`, the Laurent–Čech term) is the `twistAway` submodule of Stacks 01N2
(the same generating set; `degPiece` is its span). -/
theorem degPiece_eq_twistAway (S : Finset (Fin (N + 1))) (hS : 0 < S.card) (d : ℤ) :
    degPiece R N S d = twistAway (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (prodX_mem R N S) hS d := by
  apply le_antisymm
  · rw [degPiece, Submodule.span_le]
    rintro x ⟨j, i, a, ha, hi, rfl⟩
    exact ⟨i, j, a, ha, hi, rfl⟩
  · rintro x ⟨p, k, a, ha, hp, rfl⟩
    exact Submodule.subset_span ⟨k, p, a, ha, hp, rfl⟩

variable (d : ℤ)

/-- `T_σ : (R[T]_{T_σ})_d →+ Γ(O(d), ⋂_j D_+(T_{σ j}))`, `a/T_σ^j ↦ (z ↦ a/T_σ^j ∈ R[T]_z)`. -/
def termToSection (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    Term R N d (V N p σ) →+ Γ(projectiveSpaceOverTwist R N d, ⨅ j, chart N R (σ j)) where
  toFun y := twistSectionOn (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (prodX_mem R N _)
    (card_pos N p σ) d (⨅ j, chart N R (σ j)) (iInf_chart_eq R N p σ).le
    (LinearEquiv.ofEq _ _ (degPiece_eq_twistAway R N _ (card_pos N p σ) d) y)
  map_zero' := by
    rw [map_zero]
    exact twistSectionOn_zero _ _ _ _ _ _
  map_add' y y' := by
    rw [map_add]
    exact twistSectionOn_add _ _ _ _ _ _ _ _

theorem termToSection_apply_val (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) (y : Term R N d (V N p σ))
    (z : (⨅ j, chart N R (σ j) : (ProjectiveSpaceOver N R).Opens)) :
    (termToSection R N d p σ y).1 z =
      toFiber (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        ⟨z.1, (iInf_chart_eq R N p σ).le z.2⟩ (y : Loc R N (OrderDual.ofDual (V N p σ))) := rfl

/-- `T_{σ 0}` is a degree-one factor of `T_σ`: `T_σ = T_{σ 0} · ∏_{j ≠ 0} T_{σ j}`. -/
theorem prodX_eq_X_mul (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    prodX R N (Finset.univ.map σ.toEmbedding) =
      MvPolynomial.X (σ 0) * prodX R N ((Finset.univ.map σ.toEmbedding).erase (σ 0)) := by
  have h : σ 0 ∈ Finset.univ.map σ.toEmbedding := Finset.mem_map_of_mem _ (Finset.mem_univ 0)
  exact (Finset.mul_prod_erase _ _ h).symm

theorem prodX_erase_mem (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    prodX R N ((Finset.univ.map σ.toEmbedding).erase (σ 0)) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R ((Finset.univ.map σ.toEmbedding).card - 1) := by
  have h : σ 0 ∈ Finset.univ.map σ.toEmbedding := Finset.mem_map_of_mem _ (Finset.mem_univ 0)
  have h' := prodX_mem R N ((Finset.univ.map σ.toEmbedding).erase (σ 0))
  rwa [Finset.card_erase_of_mem h] at h'

/-- **Stacks 01MN for `P^N_R`**: `(R[T]_{T_σ})_d → Γ(O(d), ⋂_j D_+(T_{σ j}))` is bijective. -/
theorem termToSection_bijective (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    Function.Bijective (termToSection R N d p σ) :=
  (twistSectionOn_bijective (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (prodX_mem R N _)
    (card_pos N p σ) d ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R (σ 0)))
    (prodX_erase_mem R N p σ) (prodX_eq_X_mul R N p σ) _ (iInf_chart_eq R N p σ)).comp
    (LinearEquiv.ofEq _ _ (degPiece_eq_twistAway R N _ (card_pos N p σ) d)).bijective

/-- The term isomorphism `e_σ : Γ(O(d), ⋂_j D_+(T_{σ j})) ≃+ (R[T]_{T_σ})_d` (inverse of `termToSection`). -/
def termEquiv (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    Γ(projectiveSpaceOverTwist R N d, ⨅ j, chart N R (σ j)) ≃+ Term R N d (V N p σ) :=
  (AddEquiv.ofBijective (termToSection R N d p σ) (termToSection_bijective R N d p σ)).symm

theorem termEquiv_symm_apply (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) (y : Term R N d (V N p σ)) :
    (termEquiv R N d p σ).symm y = termToSection R N d p σ y := rfl

/-- Compatibility with the Čech face restrictions: restricting `a/T_{σ}^j` from `U_{τ minus k}` to `U_τ` is the
Laurent–Čech restriction `res` (both are "the same fraction in `R[T]_z`" at every point `z`). -/
theorem map_termToSection (p : ℕ) (τ : Fin (p + 2) ↪o Fin (N + 1)) (k : Fin (p + 2))
    (y : Term R N d (V N p (CechAltAlg.face τ k))) :
    (projectiveSpaceOverTwist R N d).presheaf.map
        (homOfLE (cech_face_le (chart N R) τ k)).op (termToSection R N d p (CechAltAlg.face τ k) y) =
      termToSection R N d (p + 1) τ (res d (hface N p τ k) y) := by
  apply Subtype.ext
  funext z
  change toFiber (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      ⟨z.1, (iInf_chart_eq R N p (CechAltAlg.face τ k)).le (cech_face_le (chart N R) τ k z.2)⟩
      (y : Loc R N (OrderDual.ofDual (V N p (CechAltAlg.face τ k)))) =
    toFiber (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      ⟨z.1, (iInf_chart_eq R N (p + 1) τ).le z.2⟩
      (locRes (hface N p τ k) (y : Loc R N (OrderDual.ofDual (V N p (CechAltAlg.face τ k)))))
  exact (toFiber_map_eq _ (locRes (hface N p τ k)).toRingHom (fun a ↦ locRes_algebraMap _ a) _ _ _).symm

/-- The pointwise value of the scalar section `scalar N R V r`: the constant fraction `r/1`
(Mathlib `Proj.toSpecZero` through `zeroToGlobal`). -/
theorem scalar_apply_val (V : (ProjectiveSpaceOver N R).Opens) (r : R) (z : V) :
    ((scalar N R V r).1 z).val = Localization.mk (MvPolynomial.C r) 1 := by
  have h1 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpecBase N R).appTop) r =
      AlgebraicGeometry.Proj.zeroToGlobal (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) r) := by
    rw [CommRingCat.comp_apply]
    unfold toSpecBase
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    erw [Scheme.SpecMap_appTop_ΓSpecIso_inv]
    exact AlgebraicGeometry.Proj.toSpecZero_appTop_ΓSpecIso_inv _ _
  change ((((ProjectiveSpaceOver N R).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpecBase N R).appTop).hom r)).1 z).val = _
  rw [h1]
  erw [AlgebraicGeometry.Proj.res_apply]
  rw [AlgebraicGeometry.Proj.zeroToGlobal_apply_val]
  rfl

/-- `R`-linearity of `termToSection`: `scalar r • (z ↦ y) = (z ↦ r • y)`. -/
theorem scalar_smul_termToSection (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) (r : R)
    (y : Term R N d (V N p σ)) :
    scalar N R (⨅ j, chart N R (σ j)) r • termToSection R N d p σ y = termToSection R N d p σ (r • y) := by
  apply Subtype.ext
  funext z
  change ((scalar N R (⨅ j, chart N R (σ j)) r).1 z).val * (termToSection R N d p σ y).1 z = _
  rw [scalar_apply_val, termToSection_apply_val, termToSection_apply_val, Submodule.coe_smul,
    toFiber_smul]
  rfl

end Terms

/-- **The Čech terms of `O(d)` are Laurent–Čech terms.**
There is a family of additive isomorphisms `e p σ : Γ(O(d), ⋂_j D_+(T_{σ j})) ≃+ (R[T]_{T_σ})_d`,
(1) compatible with the restrictions along Čech face maps: `e τ (x|_{U_τ}) = res (e (τ minus k) x)`;
(2) `R`-linear.
Indices, face maps and signs are literally those of `cechFamilyD` / `CechAltAlg.d`
(`Fin (p+1) ↪o Fin (N+1)`, `CechAltAlg.face`), so `cechFamilyD_eq_δ` below is a direct consequence.
Edge cases: for the zero ring `P^N_R` is empty and both sides are zero; for `N = 0` there is only the
term `p = 0`; for `p + 1 > N + 1` there are no indices and `e` is the empty function.
Proof: `e p σ := termEquiv R N d p σ`, the inverse of the bijection `termToSection` of Stacks 01MN
(`a/T_σ^j ↦ (z ↦ a/T_σ^j ∈ S_z)`); (1) and (2) reduce to the two pointwise identities
`map_termToSection` and `scalar_smul_termToSection` above.
Source: Stacks 01MN, 01MK, 01XT. -/
theorem exists_cechFamily_equiv_laurent (R : Type u) [CommRing R] (N : ℕ) (d : ℤ) :
    ∃ e : ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)),
        Γ(projectiveSpaceOverTwist R N d, ⨅ j, ProjectiveSpaceOver.chart N R (σ j)) ≃+
          LaurentCech.Term R N d (LaurentCech.V N p σ),
      (∀ (p : ℕ) (τ : Fin (p + 2) ↪o Fin (N + 1)) (k : Fin (p + 2))
          (x : Γ(projectiveSpaceOverTwist R N d,
            ⨅ j, ProjectiveSpaceOver.chart N R ((CechAltAlg.face τ k) j))),
        e (p + 1) τ ((projectiveSpaceOverTwist R N d).presheaf.map
            (homOfLE (cech_face_le (ProjectiveSpaceOver.chart N R) τ k)).op x) =
          LaurentCech.res d (LaurentCech.hface N p τ k) (e p (CechAltAlg.face τ k) x)) ∧
      (∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) (r : R)
          (x : Γ(projectiveSpaceOverTwist R N d, ⨅ j, ProjectiveSpaceOver.chart N R (σ j))),
        e p σ (scalar N R (⨅ j, ProjectiveSpaceOver.chart N R (σ j)) r • x) = r • e p σ x) := by
  refine ⟨termEquiv R N d, ?_, ?_⟩
  · intro p τ k x
    obtain ⟨y, rfl⟩ := (termEquiv R N d p (CechAltAlg.face τ k)).symm.surjective x
    rw [termEquiv_symm_apply, map_termToSection]
    show termEquiv R N d (p + 1) τ ((termEquiv R N d (p + 1) τ).symm
        (LaurentCech.res d (LaurentCech.hface N p τ k) y)) =
      LaurentCech.res d (LaurentCech.hface N p τ k) (termEquiv R N d p (CechAltAlg.face τ k)
        ((termEquiv R N d p (CechAltAlg.face τ k)).symm y))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  · intro p σ r x
    obtain ⟨y, rfl⟩ := (termEquiv R N d p σ).symm.surjective x
    rw [termEquiv_symm_apply, scalar_smul_termToSection]
    show termEquiv R N d p σ ((termEquiv R N d p σ).symm (r • y)) =
      r • termEquiv R N d p σ ((termEquiv R N d p σ).symm y)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Under any family `e` satisfying the compatibilities above, the alternating differential on families
of sections equals the Laurent–Čech differential. -/
theorem cechFamilyD_eq_δ (R : Type u) [CommRing R] (N : ℕ) (d : ℤ)
    (e : ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)),
        Γ(projectiveSpaceOverTwist R N d, ⨅ j, ProjectiveSpaceOver.chart N R (σ j)) ≃+
          LaurentCech.Term R N d (LaurentCech.V N p σ))
    (he : ∀ (p : ℕ) (τ : Fin (p + 2) ↪o Fin (N + 1)) (k : Fin (p + 2))
          (x : Γ(projectiveSpaceOverTwist R N d,
            ⨅ j, ProjectiveSpaceOver.chart N R ((CechAltAlg.face τ k) j))),
        e (p + 1) τ ((projectiveSpaceOverTwist R N d).presheaf.map
            (homOfLE (cech_face_le (ProjectiveSpaceOver.chart N R) τ k)).op x) =
          LaurentCech.res d (LaurentCech.hface N p τ k) (e p (CechAltAlg.face τ k) x))
    (q : ℕ) (t : CechFamily (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) q) :
    (fun τ => e (q + 1) τ (cechFamilyD (ProjectiveSpaceOver.chart N R)
        (projectiveSpaceOverTwist R N d) q t τ)) =
      LaurentCech.δ R N d q (fun σ => e q σ (t σ)) := by
  funext τ
  rw [LaurentCech.δ, CechAltAlg.d_apply]
  show e (q + 1) τ (∑ k : Fin (q + 2), _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, he]

/-- Except when `q + 1 = N ∧ d ≤ −(N+1)`, the alternating Čech complex of `O(d)` on the standard cover of
`P^N_R` has zero homology in degree `q + 1`. Assembled from `exists_cechFamily_equiv_laurent`,
`LaurentCech.exists_δ_eq` and `cechComplexAlt_homology_subsingleton_of_family`. -/
theorem subsingleton_cechComplexAlt_homology_succ (R : Type u) [CommRing R] (N : ℕ) (d : ℤ) (q : ℕ)
    (hq : ¬ (q + 1 = N ∧ d ≤ -((N : ℤ) + 1))) :
    Subsingleton (((cechComplexAlt (ProjectiveSpaceOver.chart N R)
      (projectiveSpaceOverTwist R N d)).homology (((q + 1 : ℕ) : ℤ))) : Type u) := by
  obtain ⟨e, he, -⟩ := exists_cechFamily_equiv_laurent R N d
  apply cechComplexAlt_homology_subsingleton_of_family
  intro s hs
  have h1 := cechFamilyD_eq_δ R N d e he (q + 1) s
  have hz : LaurentCech.δ R N d (q + 1) (fun σ => e (q + 1) σ (s σ)) = 0 := by
    rw [← h1, hs]
    funext τ
    exact map_zero _
  obtain ⟨t', ht'⟩ := LaurentCech.exists_δ_eq R N d q hq _ hz
  refine ⟨fun σ => (e q σ).symm (t' σ), ?_⟩
  have h0 := cechFamilyD_eq_δ R N d e he q (fun σ => (e q σ).symm (t' σ))
  simp only [AddEquiv.apply_symm_apply] at h0
  rw [ht'] at h0
  funext τ
  exact (e (q + 1) τ).injective (congrFun h0 τ)

end ProjectiveSpaceOver

end
