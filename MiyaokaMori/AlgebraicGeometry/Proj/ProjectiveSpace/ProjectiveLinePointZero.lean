import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjDegreeZeroIsoBase
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.RationalPointDef
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineBasicOpenExt

/-! # The marked point `0` of the projective line

The marked point `0 = [0 : 1]` of `P¹_k`, i.e. the point corresponding to the relevant homogeneous
prime ideal `(x₀)`, together with the section `Spec k → P¹_k` exhibiting it as a `k`-rational point
(the point `0` in `b(0) = x` of the main theorem of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def ProjectiveLine.zero (k : Type u) [Field k] : ProjectiveLine k :=
  (⟨⟨Ideal.span {MvPolynomial.X (0 : Fin 2)},
      Ideal.homogeneous_span _ _ (by
        rintro _ rfl
        exact ⟨1, (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k 0)⟩)⟩,
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero _)).2 MvPolynomial.X_prime,
    fun h => by
      have h1 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ∈
          (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toIdeal :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
          ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k 1))
      have h2 := h h1
      change (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ∈
        Ideal.span {MvPolynomial.X (0 : Fin 2)} at h2
      rw [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X] at h2
      exact absurd h2 (by decide)⟩ :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) k))

/-- Evaluation `x₀ ↦ 0`, `x₁ ↦ 1` (the point `[0 : 1]`) into `Γ(Spec k, ⊤)`. -/

noncomputable def ProjectiveLine.zeroEvaluation (k : Type u) [Field k] :
    MvPolynomial (Fin 2) k →+* Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp
    (MvPolynomial.eval ![0, 1])

theorem ProjectiveLine.zeroEvaluation_irrelevant (k : Type u) [Field k] :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toIdeal.map
      (ProjectiveLine.zeroEvaluation k) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hX : MvPolynomial.X (1 : Fin 2) ∈
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X k 1)
  have hmem := Ideal.mem_map_of_mem (ProjectiveLine.zeroEvaluation k) hX
  simpa [ProjectiveLine.zeroEvaluation] using hmem

noncomputable def ProjectiveLine.zeroSection (k : Type u) [Field k] :
    AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ ProjectiveLine k :=
  AlgebraicGeometry.Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (ProjectiveLine.zeroEvaluation k) (ProjectiveLine.zeroEvaluation_irrelevant k)

set_option backward.isDefEq.respectTransparency false in
theorem ProjectiveLine.zeroSection_comp (k : Type u) [Field k] :
    ProjectiveLine.zeroSection k ≫ ProjectiveSpace.toSpecBase 1 k = 𝟙 _ := by
  change ProjectiveLine.zeroSection k ≫
      (AlgebraicGeometry.Proj.toSpecZero
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin 2) k 0)))) = _
  rw [← Category.assoc, ProjectiveLine.zeroSection,
    AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero, Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have heval : ((ProjectiveLine.zeroEvaluation k).comp
      (algebraMap (MvPolynomial.homogeneousSubmodule (Fin 2) k 0)
        (MvPolynomial (Fin 2) k))).comp (algebraMap k
          (MvPolynomial.homogeneousSubmodule (Fin 2) k 0)) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := by
    ext c
    simp [ProjectiveLine.zeroEvaluation]
  rw [heval]
  exact AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of k)

private lemma support_d0_eq {k : Type u} [Field k]
    {f : MvPolynomial (Fin 2) k} {n : ℕ}
    (hf : f.IsHomogeneous n) {d : Fin 2 →₀ ℕ} (hd : d ∈ f.support)
    (hd0 : d 0 = 0) : d = Finsupp.single 1 n := by
  have hdeg := hf (MvPolynomial.mem_support_iff.mp hd)
  have hdeg' : d 0 + d 1 = n := by
    change d.sum (fun i c => c • (1 : ℕ)) = n at hdeg
    rw [Finsupp.sum_fintype d (fun i c => c • (1 : ℕ)) (by simp)] at hdeg
    simpa [smul_eq_mul, Fin.sum_univ_two] using hdeg
  have h1 : d 1 = n := by omega
  apply Finsupp.ext
  intro i
  fin_cases i
  · simpa using hd0
  · simpa using h1

private lemma eval_eq_coeff_of_mem {k : Type u} [Field k]
    {f : MvPolynomial (Fin 2) k} {n : ℕ}
    (hf : f.IsHomogeneous n) {d : Fin 2 →₀ ℕ} (hd : d ∈ f.support)
    (hd0 : d 0 = 0) :
    MvPolynomial.eval (![0, 1] : Fin 2 → k) f = f.coeff d := by
  have hdform : d = Finsupp.single 1 n := support_d0_eq hf hd hd0
  rw [MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.sum_eq_single d]
  · simp [hd0]
  · intro e he heq
    have he0 : e 0 ≠ 0 := by
      intro he0
      have heform := support_d0_eq hf he he0
      exact heq (heform.trans hdform.symm)
    rw [zero_pow he0]
    simp
  · intro hdn
    exact (hdn hd).elim

private lemma homogeneous_eval_mem_span {k : Type u} [Field k]
    {f : MvPolynomial (Fin 2) k} {n : ℕ}
    (hf : f.IsHomogeneous n)
    (he : MvPolynomial.eval (![0, 1] : Fin 2 → k) f = 0) :
    f ∈ Ideal.span {MvPolynomial.X (0 : Fin 2)} := by
  have hset : (MvPolynomial.X '' ({(0 : Fin 2)} : Set (Fin 2))) =
      ({MvPolynomial.X (0 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) := by
    ext x
    simp
  rw [← hset, MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  by_contra hd0
  have hd00 : d (0 : Fin 2) = 0 :=
    Nat.eq_zero_of_not_pos (by simpa using hd0)
  have hcoeff : f.coeff d = 0 := by
    have heq := eval_eq_coeff_of_mem hf hd hd00
    rw [he] at heq
    exact heq.symm
  exact (by simpa [MvPolynomial.mem_support_iff, hcoeff] using hd)

private lemma zero_mem_basicOpen_iff {k : Type u} [Field k]
    {n : ℕ} {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous n) :
    (ProjectiveLine.zero k : ProjectiveLine k) ∈
        AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) f ↔
      MvPolynomial.eval ![0, 1] f ≠ 0 := by
  change f ∉ Ideal.span ({MvPolynomial.X (0 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) ↔ _
  constructor
  · intro hnot he
    exact hnot (homogeneous_eval_mem_span hf he)
  · intro he hmem
    have hker : Ideal.span ({MvPolynomial.X (0 : Fin 2)} :
        Set (MvPolynomial (Fin 2) k)) ≤
        RingHom.ker (MvPolynomial.eval (![0, 1] : Fin 2 → k)) := by
      rw [Ideal.span_le]
      intro z hz
      rcases hz with rfl
      simp
    exact he (RingHom.mem_ker.mp (hker hmem))

theorem ProjectiveLine.zeroSection_base (k : Type u) [Field k]
    (p : AlgebraicGeometry.Spec (CommRingCat.of k)) :
    (ProjectiveLine.zeroSection k).base p = ProjectiveLine.zero k := by
  have hp : p = IsLocalRing.closedPoint k := by
    apply Subsingleton.elim
  subst p
  change ((ProjectiveLine.zeroSection k).base (IsLocalRing.closedPoint k) :
      ProjectiveLine k) =
    (ProjectiveLine.zero k : ProjectiveLine k)
  apply AlgebraicGeometry.Proj.ProjectiveLineBasicOpenExt.point_eq_of_pos_homogeneous_basicOpen
  intro n hn f hf
  have hzero := zero_mem_basicOpen_iff hf
  change IsLocalRing.closedPoint k ∈
      (ProjectiveLine.zeroSection k) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) f ↔ _
  have hpre :
      (ProjectiveLine.zeroSection k) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) f =
      (AlgebraicGeometry.Spec (CommRingCat.of k)).basicOpen
        (ProjectiveLine.zeroEvaluation k f) := by
    change (AlgebraicGeometry.Proj.fromOfGlobalSections
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (ProjectiveLine.zeroEvaluation k)
      (ProjectiveLine.zeroEvaluation_irrelevant k)) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) f = _
    exact AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hf
  rw [hpre, AlgebraicGeometry.basicOpen_eq_of_affine']
  change (IsLocalRing.closedPoint k : PrimeSpectrum k) ∈ PrimeSpectrum.basicOpen
      ((ConcreteCategory.hom
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).hom)
        (ProjectiveLine.zeroEvaluation k f)) ↔ _
  rw [PrimeSpectrum.mem_basicOpen]
  change (ConcreteCategory.hom
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).hom)
      (ProjectiveLine.zeroEvaluation k f) ∉
      (IsLocalRing.closedPoint k).asIdeal ↔ _
  have hevalmem :
      (ConcreteCategory.hom
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).hom)
          (ProjectiveLine.zeroEvaluation k f) ∉
        (IsLocalRing.closedPoint k).asIdeal ↔
      MvPolynomial.eval ![0, 1] f ≠ 0 := by
    simp [ProjectiveLine.zeroEvaluation, IsLocalRing.closedPoint,
      IsLocalRing.maximalIdeal_eq_bot]
  rw [hevalmem]
  exact hzero.symm

end
